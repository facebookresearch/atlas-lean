# Reverse unit propagation for pseudo-Boolean constraints

A pseudo-Boolean constraint $C$ is derivable by *reverse unit propagation* (RUP) from a database $\mathcal{D}$ of constraints if starting from the negation $\neg C$ (itself a pseudo-Boolean constraint) and repeatedly assigning literals propagated by constraints of $\mathcal{D} \cup \{\neg C\}$ under the current partial assignment, some constraint becomes falsified (negative slack). Then every assignment satisfying $\mathcal{D}$ satisfies $C$. With hints the propagation visits a given ordered list of constraints.

## Depends on

- [Pseudo-Boolean constraints in normalized form](pseudo-boolean-constraints.md)
- [RUP and RAT clauses](../rup-and-rat-clauses.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
