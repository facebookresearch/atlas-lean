# Failure of Euclidean harmonic-dimension comparison at an integer growth degree

For some even integer $n\ge8$ and integer $k\ge2$, there is a smooth positive-definite metric $g$ on $\mathbb R^n$ which is Euclidean on a ball about $0$, is complete for its intrinsic distance $d_g$, and has nonnegative Ricci curvature. Its intrinsic open balls satisfy $\mathrm{Vol}_g(B_g(0,R))/(\omega_n R^n)\to a$ for some $0<a<1$, where $\omega_n$ is the Euclidean unit ball volume. Volume uses the usual Cartesian integral with density $\sqrt{\det g}$; distance is the infimum of lengths of $C^1$ paths. There are $1+\binom{n+k-1}{k}+\binom{n+k-2}{k-1}$ linearly independent smooth real harmonic functions $u$ (using the metric trace of the covariant Hessian), each satisfying $|u(x)|\le C_u(1+d_g(0,x))^k$ for every $x$ and some $C_u\ge0$. The integers in the selected statement are existential, not fixed to the values used in an illustrative construction.

## Depends on

- [Laplace–Beltrami operator](laplacian.md)
- [Riemannian volume](../riemannian-volume/riemannian-volume.md)
- [Ricci lower bound](../curvature-of-riemannian-manifolds/ricci-ge.md)
- Cartesian Riemannian coefficients, intrinsic distance, Ricci curvature and Laplacian, and extended-volume ratio.

## Proof depends on

- Construct one complete metric with a positive subunit asymptotic volume ratio; realize enough independent global harmonic functions with exact degree, not degree plus an error.

## Expansion

Compare the Cartesian formulas to intrinsic APIs, and isolate the harmonic separation construction and the proof of independence.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HarmonicGrowth.lean#L98-L99) (statement and local definitions).
