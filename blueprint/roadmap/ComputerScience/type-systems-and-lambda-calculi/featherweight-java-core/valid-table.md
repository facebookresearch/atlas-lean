# Valid class tables

A class table `ct` is valid exactly when it is both [well formed](well-formed.md) and passes [the per-class table check](table-ok.md): `ValidTable ct` holds iff `WellFormed ct` and `TableOk ct` both hold. Well-formedness constrains class names, references, inheritance and method signatures but does not type method bodies; the per-class check requires every listed class to be well formed, including the typing of each of its method bodies. A table can be well formed without passing it, for example when a method body is an unbound variable other than `this`.

## Sources

- Cornell University, CS 4110 Programming Languages and Logics, Lecture #30: Featherweight Java (Fall 2014), https://www.cs.cornell.edu/courses/cs4110/2014fa/lectures/lecture30.pdf.
