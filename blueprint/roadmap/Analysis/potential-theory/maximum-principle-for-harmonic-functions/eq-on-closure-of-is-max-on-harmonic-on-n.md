# Strong maximum principle for harmonic functions

Let $U$ be a bounded, open and connected subset of a finite-dimensional real inner product space,
and let $u$ be harmonic on $U$ and continuous on $\overline U$. If $u$ attains its maximum over
$\overline U$ at a point of $U$, then $u$ is constant on $\overline U$.

It strengthens the weak maximum principle: on a connected domain a
nonconstant harmonic function satisfies $u(x) < \max_{\partial U} u$ at every interior point.
Schmidt states it for path-connected open sets (the same as connected for open subsets of a normed
space); Evans's entropy notes prove it for $-\sum (a^{ij} u_{x_i})_{x_j} = 0$ and
$u \in C^2(\overline U)$ from Harnack's inequality.

## Informally uses

- [Mean-value property of harmonic functions, and its converse](harmonic-on-nhd-iff-forall-average-close.md):
  Schmidt's proof shows that the set where $u$ attains its maximum is open, using ball averages.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), Strong Maximum Principle 3.10.
- L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes, [entropy.and.PDE.pdf](https://math.berkeley.edu/~evans/entropy.and.PDE.pdf), Chapter IV.A.3, Theorem 3 (Harnack's inequality) and Corollary (strong maximum principle).
