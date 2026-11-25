# Background theories in typed first-order logic

A *typed signature* consists of a set of types and of function and relation symbols, each with a list of argument types and, for a function symbol, a result type; constants are function symbols with no arguments. Terms of each type and formulas are built from typed variables and the symbols as in first-order logic, respecting types. An *interpretation* of the signature assigns to each type a nonempty set of values, to each function symbol a function between the corresponding value sets, and to each relation symbol a relation on them.

A *background theory* $T$ for the signature is a nonempty class of interpretations: a single intended interpretation, such as linear integer arithmetic with booleans and integers, or a combination that leaves some symbols uninterpreted, such as linear integer arithmetic with uninterpreted functions and equality. For a formula $\psi$, $T \models \psi$ means that $\psi$ is true in every interpretation in $T$ under every assignment of values of the right types to its free variables.

## Sources

- R. Alur, R. Bodik, G. Juniwal, M. M. K. Martin, M. Raghothaman, S. A. Seshia, R. Singh, A. Solar-Lezama, E. Torlak and A. Udupa, "Syntax-guided synthesis", *FMCAD 2013*, IEEE, 2013, Section II (background theory)
