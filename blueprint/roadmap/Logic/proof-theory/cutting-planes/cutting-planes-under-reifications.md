# Reasoning under reifications in cutting planes

Let $\rho$ be a partial assignment written as a conjunction of literals $\bigwedge_{\ell \in \rho} \ell$. If a pseudo-Boolean constraint $D$ has a cutting planes derivation (with saturation) from the restriction $F\restriction_\rho$ of a constraint set $F$, then the implication $\bigwedge_{\ell \in \rho} \ell \Rightarrow D$, encoded as a single pseudo-Boolean constraint by adding to $D$ a large multiple of the negated guard literals, has a derivation from $F$ with $O(|\rho|)$ additional lines per line of the original derivation. Thus a proof may reason "as if reifications were not present".

## Proof sketch

Lift every line $L$ of the derivation to $\bigwedge \rho \Rightarrow L$ by adding guard terms whose coefficient exceeds the degree of $L$; addition, multiplication and saturation commute with this lifting, while division requires re-adding guard axioms before dividing.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Pseudo-Boolean constraints in normalized form](../../propositional-logic/pseudo-boolean-proof-logging/pseudo-boolean-constraints.md)

## Sources

- E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel and K. Sidorov, "Pseudo-Boolean Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram Algorithms", 30th International Conference on Principles and Practice of Constraint Programming (CP), 2024.
