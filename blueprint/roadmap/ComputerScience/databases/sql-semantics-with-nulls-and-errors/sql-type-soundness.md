# Type soundness and safety for SQL expressions

On every row conforming to $\Gamma$, an expression of type $\tau$ never raises $\mathsf{typeMismatch}$: it returns $\mathsf{NULL}$, returns a value of type $\tau$, or raises $\mathsf{divisionByZero}$. A safe expression succeeds on every conforming row, and a safe predicate never makes a $\mathsf{WHERE}$ or $\mathsf{ON}$ clause fail. Typing and safety are preserved by renaming and by substitution of safe expressions of the right types.

## Proof sketch

Structural induction on the expression, using that each operator rule returns a well-typed datum on well-typed operands; division-safety rules out the only remaining error.

## Depends on

- [Typing and safety of SQL expressions](sql-expression-typing-and-safety.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
