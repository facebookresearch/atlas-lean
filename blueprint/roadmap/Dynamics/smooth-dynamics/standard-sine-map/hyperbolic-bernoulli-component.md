# A positive-area hyperbolic Bernoulli component of the standard map

Use the [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md) on the unit torus with normalized area $m$.
There is a $k_0>0$ such that for every $k\ge k_0$ there is a measurable $E$ of positive area with $F_k^{-1}E=E$ modulo $m$-null sets. For $m_E=m(E)^{-1}m|_E$, the map $F_k$ is ergodic, and $m_E$-almost every point has positive vector Lyapunov spectrum with stable and unstable rates $-\ell$ and $\ell$. Here no separate operator-norm limit is required.

There are $N\ge1$ and measurable sets $P_0,\ldots,P_{N-1}$ with union $E$ modulo null sets and pairwise null intersections. The image of $P_j$ agrees modulo null sets with $P_{j+1\bmod N}$ and each has measure $m(E)/N>0$. With its normalized restriction $m_{P_j}$, the iterate $F_k^N$ on each piece is isomorphic modulo null sets to a two-sided Bernoulli shift: there exist a probability $\beta$ on $\mathbb R$ and measurable measure-preserving maps in both directions between the torus with $m_{P_j}$ and $\mathbb R^{\mathbb Z}$ with $\beta^{\mathbb Z}$. They are inverse almost everywhere for their respective measures, and the encoding intertwines $F_k^N$ with $w\mapsto(i\mapsto w_{i+1})$ almost everywhere.

## Depends on

- [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md)
- [Two-sided left shift](../../ergodic-theory/mixing/two-sided-shift.md)

## Expansion

Extract a positive-area invariant ergodic component from the positive-exponent region, then prove the finite cyclic decomposition and a measure-theoretic Bernoulli isomorphism for each return iterate. Check invariance modulo area rather than pointwise set invariance, and keep the real product-alphabet law and separate probability normalization on each piece.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StandardMapComponents.lean#L21-L106) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/146.md).
- OpenAI, [Positive Metric Entropy for the Standard Map at Large Parameters](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
