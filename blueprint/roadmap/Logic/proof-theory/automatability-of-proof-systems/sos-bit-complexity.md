# Sum-of-squares proofs need not have small coefficients

There are systems of polynomial equalities and inequalities over $\mathbb{R}^n$, with constant-degree constraints and integer coefficients of polynomial bit length, that have degree-$2$ sum-of-squares refutations (or certificates of nonnegativity) but every degree-$O(1)$ sum-of-squares certificate requires coefficients of bit complexity $2^{\Omega(n)}$ (O'Donnell). Conversely, if the constraints include the Boolean axioms $x_i^2 = x_i$ and satisfy a mild ``richness'' condition, every degree-$d$ certificate can be replaced by one with coefficients of bit complexity $\operatorname{poly}(n^d)$ (Raghavendra-Weitz), so the ellipsoid method finds degree-$d$ certificates in time $n^{O(d)}$ in that case.

## Proof sketch

The counterexample forces, through a chain of quadratic constraints $x_{i+1} = x_i^2$, any certificate to contain doubly exponentially large multipliers. The positive result shows that under richness, the set of degree-$d$ pseudo-moment constraints is well-conditioned, so a certificate can be rounded to a nearby rational certificate with bounded denominators.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Automatable proof systems](automatable-proof-system.md)

## Sources

- R. O'Donnell, "SOS is not obviously automatizable, even approximately", ITCS (2017).
- P. Raghavendra, B. Weitz, "On the bit complexity of sum-of-squares proofs", ICALP (2017), arXiv:1702.05139.
