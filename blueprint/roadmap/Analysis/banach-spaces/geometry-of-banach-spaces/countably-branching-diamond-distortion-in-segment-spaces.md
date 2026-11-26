# All-pairs diamond distortion in the forest dual and infinite-tree coordinate span

Let the coordinate spaces be the forest full dual and infinite-tree closed coordinate span from [the two segment norms](midpoint-lens-tail-estimates-for-segment-norms.md). From a single edge, iterate $k$ times the replacement of each edge by countably many length-two paths with distinct new midpoints. Give each final edge length $2^{-k}$ and use shortest-path distance $d_k$.

In either coordinate space, for every $k\ge0$, any vertex map $f$ and reals $D,s$ with $s>0$, if all vertex pairs obey $s d_k(u,v)\le\|f(u)-f(v)\|\le D s d_k(u,v)$, then $1+k/4\le D^2$. The bound is unconditional and is not restricted to edge pairs.

## Depends on

- [Segment-norm models](midpoint-lens-tail-estimates-for-segment-norms.md) and the normalized diamond metric.

## Proof depends on

- Midpoint tail control and iteration across graph depth using the simultaneous pairwise bounds.

## Expansion

Isolate the midpoint separation and norm-growth recursion, preserving arbitrary positive scale and the zero-depth case. The forest bound with coefficient $1/12$ is a different comparator, and graph deductions conditional on companion inputs are not asserted here.

## Sources

- OpenAI, [DiamondDistortion comparator, headline_all_pairs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DiamondDistortion.lean#L302-L311).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
