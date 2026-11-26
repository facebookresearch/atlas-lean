# Upper density of a Euclidean sphere packing

A packing in dimension $d$ consists of a set of centers with pairwise distances at least a common separation $s>0$. The occupied region is the union of open balls of radius $s/2$ about these centers. For $R>0$, divide the volume of its intersection with the open ball $B(0,R)$ by the volume of $B(0,R)$. The upper density is the limsup of this ratio as $R\to\infty$. Denote the supremum of these upper densities over all such packings by $\Delta_d$, taken in the extended nonnegative reals.

## Implementation notes

Prove local finiteness and countability of separated centers and measurability of the occupied region; compare the radius parametrization with the existing packing-density convention.

## Sources

- [Pinned packing and density definitions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L58-L77)
