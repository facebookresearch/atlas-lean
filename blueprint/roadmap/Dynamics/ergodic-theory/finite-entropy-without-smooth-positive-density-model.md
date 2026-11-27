# A finite-entropy system with no smooth positive-density model

There exist a measurable space $X$, a probability measure $\mu$ and an ergodic bimeasurable bijection $T:X\to X$ such that $(X,\mu)$ is measure-isomorphic to $[0,1]$ with Lebesgue measure after removing measurable null sets. For each measurable $P:X\to\{0,\dots,q\}$, for every $q\ge0$, define $p_w=\mu\{x:P(T^j x)=w_j\text{ for }0\le j<n\}$ for length-$n$ words. Every such partition has a real limit of $-\sum_w p_w\log_2(p_w)/n$ as $n\to\infty$, with $0\log_2 0=0$, and one finite real number bounds all those limits. The selected comparator asserts **finite** entropy; the cited paper states the stronger zero-entropy conclusion.

No compact Hausdorff second-countable smooth manifold of any finite dimension without boundary (including dimension zero), or of any positive finite dimension with smooth boundary, supports a smooth diffeomorphism $S$ preserving a probability $\nu$ with a strictly positive smooth density in every extended chart that is conjugate to $T$ modulo null sets. In an extended chart the pushforward of the restricted measure is that smooth density times Lebesgue measure on the chart target; use absolute densities, not oriented forms, and require smoothness up to boundary. Conjugacy means a measure-preserving bimeasurable bijection $e:A\to B$ between measurable conull subsets with $T^{-1}A=A$, $S^{-1}B=B$ and $e(Tx)=S(e(x))$ for $x\in A$. No orientability condition is imposed.

## Depends on

- [Kolmogorov–Sinai entropy](kolmogorov-sinai-entropy/ks-entropy.md)
- [Isomorphism modulo null sets](kolmogorov-sinai-entropy/is-isomorphic-mod0.md)

## Expansion

1. Relate the finite normalized block limits and their common upper bound in bits to the Kolmogorov–Sinai entropy of a probability-preserving automorphism. Compare whole-space almost-everywhere maps with invariant-conull measurable equivalences before replacing the stated conjugacy.
2. Separate the closed and half-space chart-density models, including zero-dimensional closed manifolds and nonorientable positive-dimensional manifolds. Prove strict positivity and smoothness transfer between overlapping charts via the absolute Jacobian.
3. Extract the finite-entropy witness and the measurable invariant that excludes every such smooth positive-density realization.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SmoothObstruction.lean#L11-L95) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/152.md).
- OpenAI, [A zero-entropy system without a smooth positive-volume model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf) (September 25, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
