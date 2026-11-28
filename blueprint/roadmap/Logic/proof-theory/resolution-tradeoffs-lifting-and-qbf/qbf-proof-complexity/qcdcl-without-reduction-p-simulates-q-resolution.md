# QCDCL without reduction polynomially simulates Q-resolution

A QCDCL variant that forbids universal reduction during unit propagation and allows arbitrary existential decisions polynomially simulates Q-resolution with $O(n^3 |\pi|)$ size overhead for any asserting learning scheme, making it polynomially equivalent to Q-resolution.

**Theorem.** $\mathsf{QCDCL}^{\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}}_{\mathsf{NO\text{-}RED}}$ polynomially simulates Q-resolution: every Q-resolution refutation $\pi$ of a QCNF in $n$ variables can be transformed into a $\mathsf{QCDCL}^{\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}}_{\mathsf{NO\text{-}RED}}$ refutation of size $O(n^3 |\pi|)$ using an arbitrary asserting learning scheme. In particular, Q-resolution, $\mathsf{QCDCL}^{\mathsf{ANY}}_{\mathsf{NO\text{-}RED}}$ and $\mathsf{QCDCL}^{\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}}_{\mathsf{NO\text{-}RED}}$ are polynomially equivalent.

## Expansion

Forbidding universal reduction during propagation prevents universal tautologies from being learned, and freeing the decision order lets the solver follow the clauses of $\pi$ one by one. For each clause of $\pi$, the simulation drives the clause to become unreliable in $O(n^3)$ trail steps and restarts before moving to the next clause, terminating once the empty clause is derived. Restricting to purely existential prefixes yields the $O(n^3 |\pi|)$ propositional CDCL simulation of resolution.

## Depends on

- [QCDCL proof systems](qcdcl-proof-systems.md)
- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Theorem 6.9 and Section 6; policy names as in this edition).
