# Perfect sketches preserve the order of stored keys

For keys $x_1 < \dots < x_k$ and their significant bits, the perfect sketch is strictly increasing on the keys: $\mathrm{sketch}(x_1) < \dots < \mathrm{sketch}(x_k)$. It need not preserve the position of an arbitrary query $q$ among the keys.

## Proof sketch

For $i < j$, let $b$ be the most significant bit where $x_i$ and $x_j$ differ; it is the most significant differing bit of some adjacent pair between them, hence significant. The keys agree above $b$, so their sketches agree on all significant bits above $b$, and $x_j$ has a one at $b$ while $x_i$ has a zero.

## Depends on

- [Significant bits and perfect sketch of a key set](perfect-sketch-of-a-key-set.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
