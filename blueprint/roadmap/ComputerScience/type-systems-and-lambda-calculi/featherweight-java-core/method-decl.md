# Method declarations

A method declaration records its return class, its parameters as an ordered list of pairs (parameter class, variable name), and its body expression. The order of the parameters matters: it fixes the signature and the order of the formal names used at invocation. The method's name is not part of the record; the containing [class declaration](class-decl.md) pairs the name with it. The return class is a class name, distinct from the body expression that the method returns.

## Sources

- Cornell University, CS 4110 Programming Languages and Logics, Lecture #30: Featherweight Java (Fall 2014), https://www.cs.cornell.edu/courses/cs4110/2014fa/lectures/lecture30.pdf.
