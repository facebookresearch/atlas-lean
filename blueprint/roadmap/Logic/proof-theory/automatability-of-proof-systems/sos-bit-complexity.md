# Sum-of-squares proofs need not have small coefficients

There are systems of polynomial equalities and inequalities over $\mathbb{R}^n$, with constant-degree constraints and integer coefficients of polynomial bit length, that have degree-$2$ sum-of-squares refutations (or certificates of nonnegativity) but every degree-$2$ certificate requires coefficients of bit complexity $2^{\Omega(n)}$, although degree-$4$ certificates of polynomial bit complexity exist (O'Donnell). Raghavendra and Weitz give such a system that includes the Boolean axioms $x_i^2 = x_i$ and in which every certificate of degree at most $\sqrt{n}$ has coefficients of bit complexity $2^{\Omega(\sqrt{n})}$. Conversely, if the solutions robustly satisfy the inequalities, polynomial calculus is complete and efficient over them and they are spectrally rich, every degree-$d$ certificate can be replaced by one of degree $O(d)$ with coefficients of bit complexity $\operatorname{poly}(n^d)$ (Raghavendra-Weitz), so the ellipsoid method finds certificates of degree $O(d)$ in time $n^{O(d)}$ in that case.

## Proof sketch

The counterexample forces, through a chain of quadratic constraints $x_{i+1} = x_i^2$, any degree-$2$ certificate to contain doubly exponentially large multipliers. The positive result shows that under richness, the set of degree-$d$ pseudo-moment constraints is well-conditioned, so a certificate can be rounded to a nearby rational certificate with bounded denominators.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Sources

- R. O'Donnell, "SOS is not obviously automatizable, even approximately", ITCS (2017).
- P. Raghavendra, B. Weitz, "On the bit complexity of sum-of-squares proofs", ICALP (2017), arXiv:1702.05139.
