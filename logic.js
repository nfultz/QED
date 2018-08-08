//    Written by Terence Tao.  This work is licensed under a Creative Commons Attribution 4.0 International License: http://creativecommons.org/licenses/by/4.0/

/// Global variables

sentences = [];  // sentences[name] is a sentence attached to a name string; easier to populate this dynamically than to create a general string to sentence parser.  Also does terms
unlockedLaws = [];
numLaws = 0;  // used to give each law a numerical index with which to detect circularity

// convert a list of sentences, boxes, or contexts to a string
function listToString(list) {
    if (list.length == 0) return "";
    var i;
    var str = "";

    for (i = 0; i < list.length; i++) {
        str += toContext(list[i]).name()  + ", ";
    }
    str = str.substring(0, str.length - 2);
    return str;
}

// create a deduction string
function deductionString(prefix, list, conclusion)
{
 if (list.length == 0) {
    if (conclusion.type == "environment")
        return "Form environment " + conclusion.name() + ".";
    else
        return "Deduce " + conclusion.name() + ".";
 }
 else {
    if (conclusion.type == "environment")
        return prefix + " " + listToString(list) + ": form environment " + conclusion.name() + ".";    
    else
        return prefix + " " + listToString(list) + ": deduce " + conclusion.name() + ".";    
 }
}


//// FreeVariable object

function FreeVariable(name)
{
    this.type = "free variable";
    this.subtype = name;
    this.name = name;
    this.shortText = "<I>"+name+"</I>";
    this.longText = this.shortText;
}

// the name of a free variable associated to a non-negative integer i

function FreeVariableName(i) {
    var str;
    if (i % 3 == 0) str = 'x';
    if (i % 3 == 1) str = 'y';
    if (i % 3 == 2) str = 'z';

    var j;

    for (j=0; j < (i-2)/3; j++)  str += "'";

    return str;
}


//// BoundVariable object.  In this text, it is assumed that free and bound variables have disjoint namespaces; we'll use x,y,z,x',y', etc. for free variables and X,Y,Z,X',Y',etc. for bound variables

function BoundVariable(name)
{
    this.type = "bound variable";
    this.subtype = name;
    this.name = name;
    this.shortText = "<I>"+name+"</I>";
    this.longText = this.shortText;
}

/// the name of a bound variable associated to a non-negative integer i

function BoundVariableName(i) {
    var i;
    if (i % 3 == 0) str = 'X';
    if (i % 3 == 1) str = 'Y';
    if (i % 3 == 2) str = 'Z';

    var j;

    for (j=0; j < (i-2)/3; j++)  str += "'";

    return str;
}

/// Operator object.  additionStyle is for 2-ary operators placed in between the arguments, e.g. x+y, as opposed to f(x,y).

function Operator( name, arity, additionStyle )
{
    this.type = "operator";
    this.subtype = name;
    this.text = "<I>" + name + "</I>";
    this.arity = arity;
    this.additionStyle = additionStyle;
}

/// Term object.  The only way to make a term is to use a free or bound variable, or to apply an operator with a list of terms.

function Term()
{
    this.type = "term";
    this.subtype = "";  // will be "free variable", "bound variable", "primitive", or "operator"
    this.shortText = "";
    this.longText = "";
    this.operator = "";  // the operator used (only needed for operator subtype)
    this.argList = [];  // list of args, or just the variable
}

// turn a free variable into a term
function freeVariableTerm(free)
{
  term = new Term();
  term.subtype = "free variable";
  term.shortText = free.shortText;
  term.longText = free.longText;
  term.argList = [free];
  return term;
}

// turn a bound variable into a term
function boundVariableTerm(bound)
{
  term = new Term();
  term.subtype = "bound variable";
  term.shortText = bound.shortText;
  term.longText = bound.longText;
  term.argList = [bound];
  return term;
}

// turn an operator and some arguments into a term
function operatorTerm(operator, argList)
{
    term = new Term();
    term.subtype = "operator evaluation";
    var i;
    term.operator = operator;

    for (i=0; i < term.operator.arity; i++)
        term.argList[i] = toTerm(argList[i]);

    if (term.operator.additionStyle) {
        term.shortText = term.argList[0].longText + " " + term.operator.text + " " + term.argList[1].longText;
        term.longText = "(" + term.shortText + ")";
    } else if (term.operator.arity == 0) {
        term.shortText = term.operator.text;
        term.longText = term.shortText;
    } else {
        var str = term.operator.text + "(";
        for (i = 0; i < term.operator.arity; i++ )
            str += term.argList[i].shortText + ", ";
        str = str.substring(0, str.length - 2);
        term.shortText = str + ")";
        term.longText = term.shortText; 
    }
    return term;
}

function primitiveTerm(name)
{
    term = new Term();
    term.subtype = "primitive";
    term.shortText = name;
    term.longText = name;
    return term;  
}

// turn an object into a term if possible
function toTerm(obj)
{
    if (typeof(obj) == "string") return primitiveTerm(obj);

    if (obj.type == "term") return obj;

    if (obj.type == "free variable") return freeVariableTerm(obj);

    if (obj.type == "bound variable") return boundVariableTerm(obj);

    error("Unrecognised type for conversion to term.");
}

/// Predicate object.  relationStyle is for 2-ary predicates placed in between the arguments, e.g. x=y, as opposed to P(x,y).

function Predicate( name, arity, relationStyle )
{
    this.type = "predicate";
    this.subtype = name;
    this.text = "<I>" + name + "</I>";
    this.arity = arity;
    this.relationStyle = relationStyle;
}


//// Sentence object

function Sentence() {
    this.type = "";      // "primitive", "connective", "quantifier"
    this.subtype = "";   // "AND", "OR", "NOT", "IMPLIES", "IFF" for connectives; "atomic" or "predicate" for primitives; "for all" or "there exists" for quantifiers
    this.shortText = ""; // name of sentence when used standalone
    this.longText = "";  // name of sentence when combined with other sentences
    this.argList = [];   // the list of arguments in this sentence (usually of length 0, 1, or 2)
    this.predicate = ""; // the predicate used (only relevant for predicate subtype)
}

// create an atomic sentence
function atomicSentence(name) {
    sentence = new Sentence();
    sentence.type = "primitive";
    sentence.subtype = "atomic";
    sentence.shortText = "<em>"+name+"</em>";
    sentence.longText = sentence.shortText;
    sentence.name = name;
    return sentence;
}

// create a sentence from predicate and args

function predicateSentence(predicate, argList) {
    sentence = new Sentence;
    sentence.type = "primitive";
    sentence.subtype = "predicate";
    sentence.predicate = predicate;

    var i;

    for (i=0; i < argList.length; i++)
        sentence.argList[i] = toTerm(argList[i]);
    
    if (sentence.predicate.relationStyle) {
        sentence.shortText = argList[0].longText + " " + sentence.predicate.text + " " + argList[1].longText;
        sentence.longText = "(" + sentence.shortText + ")"; 
    } else if (sentence.predicate.arity == 0) {
        sentence.shortText = sentence.predicate.text; 
        sentence.longText = sentence.shortText;
    } else {
        var str = sentence.predicate.text + "(";
        for (i = 0; i < sentence.predicate.arity; i++ )
            str += toTerm(argList[i]).shortText + ", ";
        str = str.substring(0, str.length - 2);
        sentence.shortText = str + ")";
        sentence.longText = sentence.shortText; 
    }

    sentence.name = sentence.shortText;
    return sentence;
}

// form the conjunction of two sentences
function AND( sentence1, sentence2) {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "AND";
    sentence.shortText = sentence1.longText + " AND " + sentence2.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [sentence1, sentence2];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the disjunction of two sentences
function OR( sentence1, sentence2) {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "OR";
    sentence.shortText = sentence1.longText + " OR " + sentence2.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [sentence1, sentence2];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the implication of two sentences
function IMPLIES( sentence1, sentence2) {
    sentence = new Sentence();  
    sentence.type = "connective";
    sentence.subtype = "IMPLIES";
    sentence.shortText = sentence1.longText + " IMPLIES " + sentence2.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [sentence1, sentence2];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the iff of two sentences
function IFF( sentence1, sentence2) {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "IFF";
    sentence.shortText = sentence1.longText + " IFF " + sentence2.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [sentence1, sentence2];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the negation of a sentence
function NOT( sentence1) {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "NOT";
    sentence.shortText = "NOT " + sentence1.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [sentence1];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the TRUE sentence
function TRUE() {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "TRUE";
    sentence.shortText = "TRUE";
    sentence.longText = sentence.shortText;
    sentence.argList = [];
    sentence.name = sentence.shortText;
    return sentence;
}

// form the FALSE sentence
function FALSE() {
    sentence = new Sentence();
    sentence.type = "connective";
    sentence.subtype = "FALSE";
    sentence.shortText = "FALSE";
    sentence.longText = sentence.shortText;
    sentence.argList = [];
    sentence.name = sentence.shortText;
    return sentence;
}

// a sentence of the form "for all <bound>: <predicate>"
function forAll(predicate, bound) {
    sentence = new Sentence();
    sentence.type = "quantifier";
    sentence.subtype = "for all";
    sentence.shortText = "FOR ALL " + bound.shortText + ": " + predicate.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [predicate, bound];
    sentence.name = sentence.shortText;
    return sentence;
}

// a sentence of the form "there exists <bound>: <predicate>"
function thereExists(predicate, bound) {
    sentence = new Sentence();
    sentence.type = "quantifier";
    sentence.subtype = "there exists";
    sentence.shortText = "THERE EXISTS " + bound.shortText + ": " + predicate.longText;
    sentence.longText = "(" + sentence.shortText + ")";
    sentence.argList = [predicate, bound];
    sentence.name = sentence.shortText;
    return sentence;
}

// tries to convert an obj to sentence if it can

function toSentence(obj) {
    if (typeof(obj) == 'string') return atomicSentence(obj);
    if (obj instanceof Sentence ) return obj;
    if (obj instanceof Context ) return obj.sentence;
    if (obj instanceof Law) return obj.conclusion.sentence;
    if (obj instanceof Exercise) return obj.law.conclusion.sentence;
    if (obj instanceof Assumption) return obj.sentence;
    if (obj.type == "sentenceBox") return obj.sentence;
    if (obj.type == "formulaBox") return obj.sentence;
    error("Unable to convert object to sentence.");
}


// Law object

function Law(name, givens, conclusion) {
    numLaws++;
    this.name = name;   // name of law, e.g. "EXERCISE 1"

// givens is an array of given hypotheses (can be empty).  I allow sentences as givens, so these need to be converted to contexts.
    var givenslist = [];
    givens.forEach( function(given) {
       givenslist.push(toContext(given));
    });
    this.givens = givenslist;
    
    this.conclusion = toContext(conclusion);  // given conclusion
    this.unlocked = false;         // by default the law is not unlocked
    this.string = deductionString("Given", givens, this.conclusion);
    this.desc = "<I>"+name+"</I>: " + this.string;
    this.index = numLaws;  // the order in which the law was unlocked (used to determine circularity)
    this.clone = "";  // points to the clone of the law with additional root environment, if needed

    if (localStorage)
        if (localStorage.getItem("law " + this.name) != null)
            unlock(this, localStorage.getItem("law " + this.name));

    if (allFormulas(this.givens)) {
        if (this.conclusion.type == 'sentence in environment' || this.conclusion.type == 'environment') {
            var givensClone = this.givens.slice(0);
            givensClone.push(rootEnvironmentContext());
            this.clone = new Law(this.name, givensClone, this.conclusion);
        }
    }    
}

// list the (names of) atomic primitives, free variables, bound variables, and primitive terms occurring in a law (to do: terms, predicates)

function listPrimitives(law, getPrimitives, getFreeVars, getBoundVars, getPrimTerms) {
    list = [];


    law.givens.forEach( function(item) {
        pushPrimitivesFromContext(list, toContext(item), getPrimitives, getFreeVars, getBoundVars, getPrimTerms);
    });

// usually the line below is redundant, as any primitives in conclusion should have already appeared in one of the givens, but there are some exceptions, e.g. universal introduction without specifying the bound variable
    pushPrimitivesFromContext(list, law.conclusion, getPrimitives, getFreeVars, getBoundVars, getPrimTerms);

     return list;
}

// push all the primitives from context onto list (removing duplicates)
function pushPrimitivesFromContext(list, context, getPrimitives, getFreeVars, getBoundVars, getPrimTerms) {
    if (context.type == "formula" || context.type == "sentence in environment") {
        pushPrimitivesFromSentence(list, context.sentence, getPrimitives, getFreeVars, getBoundVars, getPrimTerms);
    }
    if (context.type == "environment" || context.type == "sentence in environment") 
    {
        context.environment.forEach( function(item) {
            if (item.type == "assuming" || item.type == "setting") {
                pushPrimitivesFromSentence(list, item.sentence, getPrimitives, getFreeVars, getBoundVars,getPrimTerms);
            }
            if (item.type == "setting" || item.type == "letting") {
                if (getFreeVars) {
                    if (!list.includes(item.variable.name)) {
                        list.push(item.variable.name);
                        sentences[item.variable.name] = item.variable;  // remember the variable object associated to name

                    }    
                }
            }
        });
    }
    if (context.type == "term context") {
        pushPrimitivesFromTerm(list, context.term, getPrimitives, getFreeVars, getBoundVars,getPrimTerms);
    }
}

// push all the primitives from sentence onto list (removing duplicates)
function pushPrimitivesFromSentence(list, sentence, getPrimitives, getFreeVars, getBoundVars,getPrimTerms)
{
//    console.log("Pushing primitives from sentence " + sentence.shortText);
    if (sentence.type == "primitive")
    {
        if (getPrimitives) {
            if (!list.includes(sentence.name)) {
                list.push(sentence.name);
                sentences[sentence.name] = sentence;  // remember the sentence object associated to name
            }    
        }
        if (sentence.subtype == "predicate") {
            sentence.argList.forEach( function(arg) { pushPrimitivesFromTerm(list,arg, getPrimitives, getFreeVars, getBoundVars,getPrimTerms);} );
        }
    } else if (sentence.type == "quantifier") {
        if (getBoundVars) {
            if (!list.includes(sentence.argList[1].name)) {
                list.push(sentence.argList[1].name);
                sentences[sentence.argList[1].name] = sentence.argList[1];
            }
        }
        pushPrimitivesFromSentence(list, sentence.argList[0], getPrimitives, getFreeVars, getBoundVars,getPrimTerms);
    }
    else {
        sentence.argList.forEach( function(arg) { pushPrimitivesFromSentence(list,arg, getPrimitives, getFreeVars, getBoundVars,getPrimTerms);} );
    }
}

// push all the primitives from term onto list (removing duplicates)
function pushPrimitivesFromTerm(list, term, getPrimitives, getFreeVars, getBoundVars,getPrimTerms)
{
//    console.log("Pushing primitives from term " + term.shortText + " - " + term.subtype);

    if (term.subtype == "primitive")  {
        if (getPrimTerms) {
            if (!list.includes(term.shortText)) {
                list.push(term.shortText);
                sentences[term.shortText] = term;  // remember the variable object associated to name
            }
        }
        return;
    }

    if (term.subtype == "operator")
        term.argList.forEach( function(arg) { pushPrimitivesFromTerm(list,arg, getPrimitives, getFreeVars,getPrimTerms);} );
    
    if (term.subtype == "free variable")
        if (getFreeVars) {
//            console.log("Found free variable " + term.argList[0].name);
            if (!list.includes(term.argList[0].name)) {
                list.push(term.argList[0].name);
                sentences[term.argList[0].name] = term.argList[0];  // remember the variable object associated to name

            }
        }

    if (term.subtype == "bound variable")
        if (getBoundVars) {
            if (!list.includes(term.argList[0].name)) {
                list.push(term.argList[0].name);
                sentences[term.argList[0].name] = term.argList[0];  // remember the variable object associated to name

            }
        }
}


// returns true if all terms in givens are formulas or terms (i.e., no environment is involved)

function allFormulas(givens) {
    var i;
    for (i = 0; i < givens.length; i++) {
        if (givens[i].type != "formula" && givens[i].type != "term context") return false;
       }    
    return true;
}

// a tricky routine: tries to match arglist to the givens of a law and see what the primitives are, returning this data in an output object.  Note: for predicate logic, some of the matches need to be discarded because the conclusion does not obey scoping laws (e.g. repeated free variables, etc.). Also there may be situations where there are multiple possible substitutions (creating existential quantifier)

function matchWithGivens( arglist, law, primitives ) {

    var givens = law.givens;
    var conclusion = law.conclusion;

    var output = new Object();
    output.matches = true;  // so far, no reason to doubt a match.
    output.env = [];        // by default, the output environment will be the root one.

    primitives.forEach( function(primitive) {
        output[primitive] = "";
    });


// technically one needs to ensure that primitives and free variables avoid reserved words such as "matches".  This is unlikely to come up in practice.

    if (arglist.length != givens.length) {
        output.matches = false;
        return output;
    }

// convert everything to contexts if not already done so (this step may be redundant)

   var i;
   for (i = 0; i < givens.length; i++) {
    arglist[i] = toContext(arglist[i]);
    givens[i] = toContext(givens[i]);
   }

// check if all the givens are formulas

   if (!allFormulas(givens))
   {
    var proposedYet = false;
    var proposedEnv = [];


    for (i = 0; i < givens.length; i++) {
        if (givens[i].type == "sentence in environment" || givens[i].type == "environment") {
            if (arglist[i].environment.length < givens[i].environment.length) {
                // can't match if the template has more deeply nested assumptions than the arglist!
                output.matches = false;
                return output;
            }
            var candidateEnv = arglist[i].environment.slice( 0, arglist[i].environment.length - givens[i].environment.length);
            if (proposedYet == false) {
                proposedYet = true;
                proposedEnv = candidateEnv;
            }  
            else if (assumptionListToString(proposedEnv) != assumptionListToString(candidateEnv)) {  // need to convert to string here as a proxy for passing by value rather than by reference
                output.matches = false;
                return output;
            }    
        }
    }
    output.env = proposedEnv;
   }

    if (law == universalIntroduction || law == universalIntroduction2)  // this family of laws is treated separately
    {
        matchUniversalIntroduction(arglist, output, law);
        if (!output.matches) return output;
    }
    else if (law == universalSpecification)  {  // this law is also treated separately
        matchUniversalSpecification(arglist, output, law);
        if (!output.matches) return output;
    } else {
        var i;
        for (i = 0; i < givens.length; i++) {
            matchWithGiven( arglist[i], givens[i], output)
            if (!output.matches) return output;
        }
        output.conclusion = subs(conclusion, output);
    }


    if  (!isLegal(output.conclusion)) {
        output.matches = false;
        return output;
    }

    return output;
}

// match arglist against one of the two laws of universal introduction and report the conclusions in output
function matchUniversalIntroduction(arglist, output, law) {
    if (!output.matches) return;

    // arglist[0] needs to be of the form "A, [letting x be arbitrary]" after the output.env
    if (arglist[0].type != "sentence in environment") {
        output.matches = false;
        return;
    }

    var assumption = arglist[0].environment[output.env.length];

    if (assumption.type != "letting") {
        output.matches = false;
        return;
    }

    var freeVariable = assumption.variable;
    var statement = arglist[0].sentence;

    var boundVariable;

    if (law == universalIntroduction) {
        if (arglist[1].type != "term context") {
            output.matches = false;
            return;
        }
        if (arglist[1].term.subtype != "bound variable") {
            output.matches = false;
            return;
        }
        boundVariable = arglist[1].term.argList[0];
    } else  if (law == universalIntroduction2) {

        if (arglist[1].type != "environment") {
            output.matches = false;
            return;
        }
        // choose the next available bound Variable
        var boundVars = [];
        
        pushPrimitivesFromSentence(boundVars, statement, false, false, true);

        var num=0;
        var match;
        
        do {
            var str = BoundVariableName(num);
            match = boundVars.includes(str);
            num++;
        } while (match);
     
        boundVariable = new BoundVariable(str);
    }

    var newSentence = forAll( freeToBound( statement, freeVariable, boundVariable), boundVariable);
    output.conclusion = sentenceContext( newSentence, output.env );
}

// replace all occurrences of free variable with bound variable in statement

function freeToBound(statement, freeVariable, boundVariable) {
    var newArgList = [];
    var i;
    
    if (statement.type == "free variable" || statement.type == "bound variable") return statement;

//    console.log("Replacing " + freeVariable.name + " with " + boundVariable.name + " in " + statement.shortText + " (" + statement.type + ", " + statement.subtype + ")");
    for (i=0; i < statement.argList.length; i++)
        newArgList[i] = freeToBound(statement.argList[i], freeVariable, boundVariable);

    if (statement.type == "term") {
        if (statement.subtype == "free variable") {
            if (statement.argList[0] != freeVariable) return statement;
            return toTerm(boundVariable);
        }
        if (statement.subtype == "bound variable") return statement;
        if (statement.subtype == "primitive") return statement;
        if (statement.subtype == "operator") return operatorTerm(statement.operator, newArgList);
    }

    if (statement.type == "primitive") {
        if (statement.subtype == "atomic") return statement;
        if (statement.subtype == "predicate") return predicateSentence(statement.predicate, newArgList);
    }
    if (statement.type == "connective") {
        if (statement.subtype == "AND") return AND( newArgList[0], newArgList[1]);
        if (statement.subtype == "OR") return OR( newArgList[0], newArgList[1]);
        if (statement.subtype == "IMPLIES") return IMPLIES( newArgList[0], newArgList[1]);
        if (statement.subtype == "IFF") return IFF( newArgList[0], newArgList[1]);
        if (statement.subtype == "NOT") return NOT( newArgList[0]);
        if (statement.subtype == "TRUE") return TRUE();
        if (statement.subtype == "FALSE") return FALSE();
    }
    if (statement.type == "quantifier") {
        if (statement.subtype == "for all") return forAll( newArgList[0], newArgList[1]);
        if (statement.subtype == "there exists ") return thereExists( newArgList[0], newArgList[1]);
    }
    output.matches = false;
    return;
}


// match arglist against the law of universal specification and report the conclusions in output
function matchUniversalSpecification(arglist, output, law) {
    if (!output.matches) return;

//    console.log("Trying universal specification with " + arglist[0].name() + " and " + arglist[1].name());

    // arglist[0] needs to be of the form "FOR ALL X: P(X)" after the output.env
    if (arglist[0].type != "sentence in environment") {
        output.matches = false;
        return;
    }

    if (arglist[0].sentence.type != "quantifier" || arglist[0].sentence.subtype != "for all") {
        output.matches = false;
        return;
    }

    var sentence = arglist[0].sentence.argList[0];
    var boundVar = toTerm(arglist[0].sentence.argList[1]).argList[0];

//    console.log("Obtained sentence " + sentence.shortText + " and bound var " + boundVar.name);

    if (arglist[1].type != "term context") {
        output.matches = false;
        return;
    }

    var term = toTerm(arglist[1].term);

    var newSentence = boundToTerm( sentence, boundVar, term );
    output.conclusion = sentenceContext( newSentence, output.env );
}

// replace all occurrences of bound variable with term in statement

function boundToTerm(statement, boundVariable, term) {
    var newArgList = [];
    var i;
    
    if (statement.type == "free variable" || statement.type == "bound variable") return statement;

//    console.log("Replacing " + boundVariable.name + " with " + term.shortText + " in " + statement.shortText + " (" + statement.type + ", " + statement.subtype + ")");
    for (i=0; i < statement.argList.length; i++)
        newArgList[i] = boundToTerm(statement.argList[i], boundVariable, term);

    if (statement.type == "term") {
        if (statement.subtype == "free variable") return statement;
        if (statement.subtype == "bound variable") {
            if (statement.argList[0] != boundVariable) return statement;
            return term;
        }
        if (statement.subtype == "primitive") return statement;
        if (statement.subtype == "operator") return operatorTerm(statement.operator, newArgList);
    }

    if (statement.type == "primitive") {
        if (statement.subtype == "atomic") return statement;
        if (statement.subtype == "predicate") return predicateSentence(statement.predicate, newArgList);
    }
    if (statement.type == "connective") {
        if (statement.subtype == "AND") return AND( newArgList[0], newArgList[1]);
        if (statement.subtype == "OR") return OR( newArgList[0], newArgList[1]);
        if (statement.subtype == "IMPLIES") return IMPLIES( newArgList[0], newArgList[1]);
        if (statement.subtype == "IFF") return IFF( newArgList[0], newArgList[1]);
        if (statement.subtype == "NOT") return NOT( newArgList[0]);
        if (statement.subtype == "TRUE") return TRUE();
        if (statement.subtype == "FALSE") return FALSE();
    }
    if (statement.type == "quantifier") {
        if (statement.subtype == "for all") return forAll( newArgList[0], newArgList[1]);
        if (statement.subtype == "there exists ") return thereExists( newArgList[0], newArgList[1]);
    }
    output.matches = false;
    return;
}


// try to match a context with a template context and store the match in output

function matchWithGiven( context, template, output) {
  if (!output.matches) return;

  if (context.type != template.type) {
    output.matches = false;
    return;
  }

  if (template.type == "environment" || template.type == "sentence in environment") {
      var i;
      for (i = 0; i < template.environment.length; i++) {
        matchWithGivenAssumption( context.environment[i + output.env.length], template.environment[i], output);      
        if (!output.matches) return;
      } 
  }

  if (template.type == "formula" || template.type == "sentence in environment")
    matchWithGivenSentence( context.sentence, template.sentence, output);

  if (template.type == "term context")
    matchWithGivenTerm( context.term, template.term, output);  
}

// try to match an assumption with a template sentence and store the match in output

function matchWithGivenAssumption( assumption, template, output) {
    if (!output.matches) return;

    if (assumption.type != template.type) {
        output.matches = false;
//         debug("Type mismatch.");
        return;
    }


    if (assumption.type == 'assuming' || assumption.type == 'setting') {
        matchWithGivenSentence( assumption.sentence, template.sentence, output);
    }

    if (assumption.type == 'letting' || assumption.type == 'setting') {
        if (assumption.variable == output[template.variable.name]) {
            // good, it matches what we've already fit to the template!
            return;
        }
        if (output[template.variable.name] == "") {
            output[template.variable.name] = assumption.variable;
            return;
        }
        output.matches = false;
        return;
    }

}

// try to match a sentence with a template sentence and store the match in output

function matchWithGivenSentence( sentence, template, output) {
    if (!output.matches) return;


    if (template.type == "primitive") { 
        if (template.subtype == "atomic") {
            if (sentence.shortText == output[template.name].shortText) {
                // good, it matches what we've already fit to the template!
                return;
            }
            if (output[template.name] == "") {
                output[template.name] = sentence;
                return;
            }
            output.matches = false;
            return;
        }
        // need some code for matching with a predicate sentence.  Right now, we simply refuse to match:
        output.matches=false;
        return;
    }

    if (template.type != sentence.type) {
//         debug("Type mismatch.");
         output.matches = false;
         return;
    }

    if (template.subtype != sentence.subtype) {
        //         debug("Type mismatch.");
        output.matches = false;
        return;
    }
        
  var len = template.argList.length;
  var i;

  for (i=0; i<len; i++) {
      matchWithGivenSentence( sentence.argList[i], template.argList[i], output);
  }
}

// try to match a term with a template sentence and store the match in output

function matchWithGivenTerm( term, template, output) {
    if (!output.matches) return;

    if (template.subtype == "free variable" || template.subtype == "bound variable") {
        if (term.subtype != template.subtype) {
            output.matches = false;
            return;
        }
        if (term.argList[0] == output[template.argList[0].name]) {
            // good, it matches what we've already fit to the template!
            return;
        }
        if (output[template.argList[0].name] == "") {
            output[template.argList[0].name] = term.argList[0];
            return;
        }
        output.matches = false;
        return;
    }

    // need some code if template is a bound variable, primitive term, or a predicate term
}

// insert the values of the output object (previously obtained by matchWithGivens) to a template sentence or term

function subsSentence(template, output)
{
 //   console.log("Substituting " + template.shortText + " - " + template.type);

    if (template.type == "free variable" || template.type == "bound variable")
    {
        return toTerm( output[template.name] );
    }

    if (template.type == "term") {
        if (template.subtype == "free variable" || template.type == "bound variable") {
            return toTerm( output[template.argList[0].name]);
        }
        if (template.subtype == "operator") {
            error("Templates with operators not currently implemented!");
            return;
        }
        if (template.subtype == "primitive") {
            error("Templates with primitive terms not currently implemented!");
            return;
        }
    }

    if (template.type == "primitive") {
        if (template.subtype == "atomic") {
            return output[template.name];
        }
        if (template.subtype == "predicate") {
            // need (rather complicated) code here.
            error("Templates with predicates not currently implemented!");
            return;
        }
    }

    if (template.type == "quantifier") {
        if (template.subtype == "for all")
            return forAll( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );

        if (template.subtype == "there exists")
            return thereExists( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );
        return;
    }
    // so now we have a connective

    if (template.subtype == "TRUE") {
        return TRUE();
    }
    if (template.subtype == "FALSE") {
        return FALSE();
    }
    if (template.subtype == "NOT") {
        return NOT( subsSentence(template.argList[0], output) );
    }
    if (template.subtype == "AND") {
        return AND( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );
    }
    if (template.subtype == "OR") {
        return OR( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );
    }
    if (template.subtype == "IMPLIES") {
        return IMPLIES( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );
    }
    if (template.subtype == "IFF") {
        return IFF( subsSentence(template.argList[0], output), subsSentence(template.argList[1], output) );
    }
}

// insert the values of the output object (previously obtained by matchWithGivens) to an environment; starts with the object ambient environment  

function subsEnvironment(env, output) {
    var list = output.env;

    env.forEach( function(item) {
        if (item.type == "assuming") {
            list.push( toAssumption(subsSentence(item.sentence, output)) );
        }
        if (item.type == "letting") {
            list.push(toAssumption( output[item.variable.name]));
        } 
        if (item.type == "setting") {
            // need code here
        }
    });
    return list;
}

// insert the values of the output object (previously obtained by matchWithGivens) to a template context

function subs(template, output)
{
    // TODO: in some laws there will be bound variables that are not currently set in output.  If so, they need to be set to first available bound variable
    // for now such laws will be coded in by hand.

    if (template.type == "formula") {
        return formulaContext(subsSentence(template.sentence, output));
    }
    if (template.type == "environment") {
        return environmentContext(subsEnvironment(template.environment, output));;
    }
    if (template.type == "sentence in environment") {
        return sentenceContext(subsSentence(template.sentence, output), subsEnvironment(template.environment, output));
    }
    error("Template type not recognised:" + template.type);
}


// assumption object

function Assumption() {
    this.type = "";  // "assuming", "letting", "setting"
    this.sentence = new Sentence();   // the sentence being assumed (for "assuming" and "setting" types)
    this.variable = new FreeVariable();    // the free variable used (for "letting" and "setting types")
    this.name = "";
}

function sentenceAssumption(sentence)
{
    var assumption = new Assumption();
    assumption.type = "assuming";
    assumption.sentence = sentence;
    assumption.name = "Assume " + sentence.shortText;
    return assumption;
}

function variableAssumption(variable)
{
    var assumption = new Assumption()
    assumption.type = "letting";
    assumption.variable = variable;
    assumption.name = "Let " + variable.shortText + " be arbitrary";
    return assumption;
}

function toAssumption(obj) {
    if (obj instanceof Assumption) return obj;

    if (obj instanceof Sentence) return sentenceAssumption(obj);

    if (obj instanceof FreeVariable) return variableAssumption(obj);

    error("Unrecognised type to convert to assumption.");
}

// convert a list of assumptions to a string

function assumptionListToString( assumptions )
{
    var currentType = "";
    var shortText = "";
    var longText = "";
    var shortHalfText = "";
    var longHalfText = "";

    if (assumptions.length == 0) return "root environment";

    assumptions.forEach( function( assumption ) {
        if (assumption.type == "assuming")
        {
            if (currentType == "assuming") {
                shortText = longText + assumption.sentence.shortText;
                longText = shortText + ", ";

            }
            else {
                shortText = longText + "assuming " + assumption.sentence.shortText;
                longText = shortText + ", ";
            }
        }
        else if (assumption.type == "letting")
        {
            if (currentType == "letting") {
                shortHalfText = longHalfText + assumption.variable.shortText;
                longHalfText = shortHalfText + ", ";
                shortText = shortHalfText + " be arbitrary";
                longText = shortText + ", ";
            } else {
                shortHalfText = longText + "letting " + assumption.variable.shortText;
                longHalfText = shortHalfText + ", ";
                shortText = shortHalfText + " be arbitrary";
                longText = shortText + ", ";

            }
        } else if (assumption.type == "setting") {
            shortText = longText + "setting " + assumption.variable.shortText + " s.t. " + assumption.sentence.shortText;
            longText = shortText + ", ";
        }
        currentType = assumption.type;
    });
    return shortText;
}

// Context object

// perhaps the most complicated object in the code.  A context is one of four things:
// A sentence inside an environment ("A [assuming B]";
// An environment ("[assuming A]", or "[Root environment]");
// A formula "Formula "A"" (a sentence without environment)
// A term (in the term window)
// A free variable (in the free variable or term window)

function Context() {
    this.type = "";      // "sentence in environment", "environment", "formula", "term context"
    this.sentence = new Sentence(); // sentence used (for sentence, sentence-in-envrionment, and formula types)
    this.environment = [];  // environment used (for sentence-in-environment and environment types); an ordered list of assumptions
    this.term = new Term();  // term used (For term context types)

    this.name = function() {
        if (this.type == "formula") {
            return 'formula "' + this.sentence.shortText + '"';
        }
        if (this.type == "term context") {
            return 'term "' + this.term.shortText + '"';
        }

        if (this.type == "environment")
        {
            return "[" + assumptionListToString(this.environment) + "]";
        }
        if (this.type == "sentence in environment")
        {
            if (this.environment.length == 0)
                return this.sentence.shortText;
            else
            {
                return this.sentence.shortText + " [" + assumptionListToString(this.environment) + "]";
            }
        }
        error("Unknown context type!");
        return "";
    }
}

// obj is either a sentence, or a string to which one can look up a sentence

function formulaContext(obj) {
  formula = new Context();
  formula.type = "formula";

  if (typeof obj == 'string')
  {
      formula.sentence = sentences[obj];
  }
  else
      formula.sentence = obj;

  return formula;
}

function termContext(obj) {
    context = new Context();
    context.type = "term context";

    if (typeof obj == 'string')
    {
        context.term = toTerm(sentences[obj]);
    }
    else
        context.term = toTerm(obj);
  
    return context;
  }
  
function sentenceContext(sentence, env) {
    context = new Context();
    context.type = "sentence in environment";
    context.sentence = sentence;
    context.environment = env;

    return context;
}

function environmentContext(env) {
    var context = new Context();
    context.type = "environment";
    context.environment = [];
    env.forEach( function(assumption) { context.environment.push(toAssumption(assumption));});
    return context;
}

function rootEnvironmentContext() {
    return environmentContext([]);
}

// create a new context from an existing context with an additional assumption.  This assumption is put at the bottom of the assumption nesting, e.g. assuming("A assuming B", C) would give "A assuming B,C"
// assumption can be a sentence, free variable, or setting a variable
function assuming(context, assumption) {
// in case one is passed a sentence or box instead of a context
    var newcontext = toContext(context);


// need a copy of newcontext.environment, otherwise push would modify the original environment.
    var envclone = newcontext.environment.slice(0);

    envclone.unshift(toAssumption(assumption));

    return sentenceContext(newcontext.sentence, envclone);
}


// checks a sentence, term, or variable is legal given the available free and bound variables.  If freeVariables = "ALL" then all free variables are legitimate.  If allowUnbound is true, allow bound variables that are not bound by quantifiers.

function isLegalSentence(obj, freeVariables, boundVariables, allowUnbound) {
    if (obj instanceof Sentence || obj instanceof Term) {

        var newBoundVariables = boundVariables.slice(0);

        if (obj.type == 'quantifier') {
            var boundVar = toTerm(obj.argList[1]).argList[0];  // the bound variable in the quantifier
            if (newBoundVariables.includes(boundVar.name)) { // uh oh, trying to bound a variable twice?
//                console.log("Repeated bound variable.");
                return false;
            } else {
                newBoundVariables.push(boundVar.name);
            }
        }

        var i;
        for (i=0; i < obj.argList.length; i++)
        {
            if (!isLegalSentence(obj.argList[i], freeVariables, newBoundVariables, allowUnbound)) return false;
        }
        return true;
    }
    if (obj instanceof FreeVariable) {
        if (freeVariables == "ALL") return true;
        else return freeVariables.includes(obj.name);
    }
    if (obj instanceof BoundVariable) {        
        if (allowUnbound) return true;
        return boundVariables.includes(obj.name);
    }
    return true;
}

// checks if a context is actually legal.  This means:
// * no repeated free variables
// * no unquantified bound variables
// * no repeated bound variables  
// * Sentence only depends on ambient free variables

function isLegal(context) {
// don't check for legality for  terms
    if (context.type == 'term context') return true;

//    console.log("Testing " + context.name() + " (" + context.type + ") for legality.");

// for formulae, bound variables not bounded by quantifiers are OK
    if (context.type == 'formula') 
        return isLegalSentence(context.sentence, "ALL", [], true);
        
    var freeVariables = [];  // list of available free variables
    var i;

    for (i=0; i<context.environment.length; i++) {
        var assumption = context.environment[i];
        if (assumption.type == "letting" || assumption.type == "setting") {
            if (freeVariables.includes(assumption.variable.name)) {
                console.log("Repeated free variable.");
                return false;  // assumptions involve repeated free variables
            } else {
                freeVariables.push(assumption.variable.name);
            }
        }
        if (assumption.type == "assuming" || assumption.type == "setting") {
            if (!isLegalSentence(assumption.sentence, freeVariables, [], false))
                return false;
        }
      }
    
    if (context.type == "sentence in environment")
        if (!isLegalSentence(context.sentence, freeVariables, [], false))
            return false;
    
    return true;
}
    

// return the list of assumptions associated to an environment box
function listAssumptions(env) {
    if (env.id == "root environment") {
        return [];
    } else {
        var list = listAssumptions(env.parentElement).slice(0);
        list.push( env.assumption );
        return list;
    }
}


// convert obj to context, where object is either a sentence, a context, or a box
function toContext(obj) {
    if (obj instanceof Sentence) {
        return sentenceContext(obj, []);
    }

    if (obj instanceof Term) {
        return termContext(obj);
    }

    if (obj instanceof Context) {
        return obj;
    }

    if (obj instanceof FreeVariable) {
        return environmentContext([ toAssumption(obj) ]);
    }

    if (obj instanceof BoundVariable) {
        return toContext(toTerm(obj));
    }

    // only remaining possibility is that it is a sentencebox, formulabox, termBox or an environment

    if (obj.type == "environment") {
        return environmentContext(listAssumptions(obj));
    }

    if (obj.type == "sentenceBox") {
        var context = sentenceContext(obj.sentence, listAssumptions(obj.parentElement));        
        return context;
    }

    if (obj.type == "formulaBox") {
        return formulaContext(obj.sentence);
    }

    if (obj.type == "termBox") {
        return termContext(obj.term);
    }

    error("Unrecognised type: " + obj.type);
    return new Context();

}






