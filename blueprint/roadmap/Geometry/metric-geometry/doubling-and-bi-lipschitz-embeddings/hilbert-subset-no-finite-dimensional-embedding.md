# A doubling subset of real ℓ² with no finite-dimensional bi-Lipschitz embedding

A subset is intrinsically $N$-doubling if every open ball of radius $r>0$ in the subset is covered by at most $N$ open balls of radius $r/2$ with centers in the subset. A bi-Lipschitz embedding at distortion $D\ge1$ means a map $f$ and a scale $a>0$ with $a d(x,y)\le d(f(x),f(y))\le Da d(x,y)$ for all points of the subset.

There is one subset $S\subset\ell^2(\mathbb N;\mathbb R)$ which is intrinsically $76800$-doubling and admits no such embedding into $\mathbb R^k$ with its Euclidean metric for any positive integer $k$. The same $S$ works for every $k$, scale, and finite distortion. Compactness is not part of this endpoint.

## Depends on

- Intrinsic open-ball covering with center restriction, $\ell^2$ norm and Euclidean target metric.

## Proof depends on

- Uniform cover counts for the selected finite configurations and dimension/distortion obstruction across their assembled scales.

## Expansion

Separate the finite metric obstructions from the Hilbert realization, then verify the exact intrinsic doubling bound after assembling a single subset.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DoublingHilbert.lean#L22-L27) (statement and local definitions).
