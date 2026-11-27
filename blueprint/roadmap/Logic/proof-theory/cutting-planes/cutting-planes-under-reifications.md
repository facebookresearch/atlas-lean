# Reasoning under reifications in cutting planes

Let $F$ be a pseudo-Boolean formula over $n$ variables and $\rho$ a partial assignment, written as a conjunction of literals $\bigwedge_{\ell \in \rho} \ell$. If a pseudo-Boolean constraint $D$ of degree $K$ has a derivation of length $L$ from the restriction $F\restriction_\rho$ using cutting planes rules (addition, multiplication, division, saturation, weakening) and RUP steps, then the implication $\bigwedge_{\ell \in \rho} \ell \Rightarrow D$, encoded as the single pseudo-Boolean constraint $\sum_{\ell \in \rho} K \bar\ell + D$, has a derivation of length $O(n \cdot L)$ from $F$. Thus a proof may reason "as if reifications were not present".

## Proof sketch

Lift every line $D_s$ of the derivation to $\bigwedge \rho \Rightarrow D_s$, with guard coefficient equal to the degree of $D_s$, by induction. An axiom $C\restriction_\rho$ is lifted from $C$ in $O(|\mathrm{Vars}(C)|)$ lines by weakening the literals fixed by $\rho$ and saturating. Multiplication, division and saturation commute with the lifting; addition is followed by one saturation, since cancellation only lowers the degree; weakening is a case of addition; and a RUP step stays a single RUP step, because propagation first sets all guard literals true.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Pseudo-Boolean constraints in normalized form](../../propositional-logic/proof-certificates/pseudo-boolean-proof-logging/pseudo-boolean-constraints.md)

## Sources

- E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel and K. Sidorov, "Pseudo-Boolean Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram Algorithms", 30th International Conference on Principles and Practice of Constraint Programming (CP 2024), LIPIcs 307, 9:1–9:21, 2024: Appendix A.2, Lemma 2 and Theorem 1.
