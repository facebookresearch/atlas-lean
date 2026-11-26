# SQL truth values form Kleene's strong three-valued logic

Order the SQL truth values $\mathsf{false} < \mathsf{unknown} < \mathsf{true}$. Then SQL's $\mathsf{AND}$ is the minimum and $\mathsf{OR}$ the maximum, so the truth values form a bounded distributive lattice (a chain), and $\mathsf{NOT}$ is the order-reversing involution fixing $\mathsf{unknown}$. De Morgan's laws hold and Kleene's law $a \wedge \neg a \le b \vee \neg b$ holds, but $\mathsf{NOT}$ is not a lattice complement: $\mathsf{unknown} \vee \neg\,\mathsf{unknown} = \mathsf{unknown}$, so excluded middle fails, and the Heyting complement of this chain (which sends $\mathsf{unknown}$ to $\mathsf{false}$) differs from $\mathsf{NOT}$. A $\mathsf{WHERE}$ or $\mathsf{ON}$ clause keeps a row exactly when its predicate is $\mathsf{true}$.

## Depends on

- [SQL nulls and three-valued logic](../bags-and-nulls/sql-nulls-and-three-valued-logic.md)

## Sources

- S. C. Kleene, "Introduction to Metamathematics", North-Holland, 1952.
- L. Libkin, "SQL's Three-Valued Logic and Certain Answers", ACM Transactions on Database Systems 41(1), 2016.
- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
