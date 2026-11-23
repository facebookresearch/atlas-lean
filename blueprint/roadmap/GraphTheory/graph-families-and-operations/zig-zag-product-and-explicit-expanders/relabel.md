# Relabelling the edges of a rotation map

Let $\mathrm{rot}$ be a [rotation map](rotation-map.md) on $V \times L$ and $e : L \to L'$ a bijection of label sets. The relabelled rotation map on $V \times L'$ is

$$(v, i') \mapsto (w, e(j)), \qquad \text{where } (w, j) = \mathrm{rot}(v, e^{-1}(i')),$$

which describes the same multigraph with the labels renamed.
