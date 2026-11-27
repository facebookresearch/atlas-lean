# Pseudo-Boolean constraints in normalized form

A *pseudo-Boolean constraint* is an inequality $\sum_i a_i \ell_i \ge d$ with natural coefficients $a_i$, literals $\ell_i$ (a variable $x$ or its negation $\bar x = 1 - x$, counted $1$ when true and $0$ when false) and a natural *degree* $d$. It is *normalized* when each variable occurs in at most one term. Its *slack* under a partial assignment $\rho$ is $\sum_{\ell_i \text{ not false under } \rho} a_i - d$; the constraint is falsified by every extension of $\rho$ iff the slack is negative, and it *propagates* a literal $\ell_i$ unset by $\rho$ when $a_i$ exceeds the slack. A clause is the constraint with all coefficients and degree $1$; every pseudo-Boolean constraint is equivalent to an integer linear inequality over $0/1$ variables.

## Depends on

- [The cutting planes proof system](../../../proof-theory/cutting-planes/cutting-planes-proof-system.md)
- [CNF clause](../../conjunctive-normal-form/cnfclause.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021.
