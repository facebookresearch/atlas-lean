# Strict semantics of SQL scalar operators

Each SQL operator maps data to a datum or fails with an error, either $\mathsf{typeMismatch}$ or $\mathsf{divisionByZero}$, according to these rules: a non-null operand of the wrong type is a type error even when the other operand is $\mathsf{NULL}$; otherwise a $\mathsf{NULL}$ operand gives $\mathsf{NULL}$ (so $\mathsf{NULL}/0 = \mathsf{NULL}$ while $1/0$ fails); integer division truncates toward zero and $\%$ takes the sign of the dividend; comparisons of two values of the same type return a truth value as a datum ($\mathsf{unknown}$ is $\mathsf{NULL}$), with integers compared numerically, text by code points and $\mathsf{false} < \mathsf{true}$; $\mathsf{AND}$, $\mathsf{OR}$, $\mathsf{NOT}$ are the Kleene connectives; $\mathsf{IS\ NULL}$ and $\mathsf{IS\ NOT\ NULL}$ never return $\mathsf{NULL}$; and $e\ \mathsf{IN}\ (v_1, \dots, v_k)$ is the Kleene disjunction of the comparisons $e = v_i$ starting from $\mathsf{false}$. All operators are strict in both operands.

## Depends on

- [SQL values, NULL and typed rows](sql-values-null-and-rows.md)
- [SQL truth values form Kleene's strong three-valued logic](sql-kleene-truth-values.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- H. Garcia-Molina, J. D. Ullman and J. Widom, "Database Systems: The Complete Book", 2nd ed., Pearson, 2008.
