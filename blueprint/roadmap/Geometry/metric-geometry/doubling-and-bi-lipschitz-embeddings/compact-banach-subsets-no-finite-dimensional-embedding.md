# Compact doubling subsets of infinite-dimensional real Banach spaces

A subset is intrinsically $N$-doubling if every open ball of radius $r>0$ in the subset is covered by at most $N$ open balls of radius $r/2$ with centers in the subset. A bi-Lipschitz embedding at distortion $D\ge1$ means a map $f$ and a scale $a>0$ with $a d(x,y)\le d(f(x),f(y))\le Da d(x,y)$ for all points of the subset.

There is one natural number $N$ such that for every infinite-dimensional real Banach space $B$ some compact $K\subset B$ is intrinsically $N$-doubling but admits no bi-Lipschitz embedding into any finite-dimensional real normed space. The obstruction quantifies over all those target spaces, not only Euclidean spaces of a fixed dimension, and the doubling bound is uniform over the ambient Banach space.

## Depends on

- Intrinsic doubling of subsets in the induced metric, completeness and finite dimensionality of real normed spaces.

## Proof depends on

- Uniform finite configurations inside arbitrary infinite-dimensional Banach spaces and a compact placement preserving obstruction and open-ball doubling.

## Expansion

Verify Euclidean-to-normed target transfer using finite-dimensional norm equivalence. Glue the finite witnesses at scales tending to zero and check compactness and the uniform cover for balls meeting multiple scales.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CompactBanach.lean#L25-L31) (statement and local definitions).
