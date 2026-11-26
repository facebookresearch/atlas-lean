# Class declarations

A class declaration consists of its class name, its superclass name, its list of typed fields (pairs of a class name and a field name), its list of constructor parameters (pairs of a class name and a field name) and its list of named methods (pairs of a method name and a [method declaration](method-decl.md)). It stores no constructor body; [class well-formedness](class-ok.md) requires the constructor parameters to be the superclass's fields followed by the class's own fields.

## Sources

- Cornell University, CS 4110 Programming Languages and Logics, Lecture #30: Featherweight Java (Fall 2014), https://www.cs.cornell.edu/courses/cs4110/2014fa/lectures/lecture30.pdf.
