# Continuity of the feature map

Let $X$ be a topological space and $H$ a real reproducing kernel Hilbert space of functions on $X$
with kernel $k$. If $(x, y) \mapsto k(x, y)$ is continuous on $X \times X$, then the [feature
map](feature-map.md) $x \mapsto \varphi(x) = k(\cdot, x)$ is continuous from $X$ to $H$, since
$\|\varphi(x) - \varphi(y)\|^2 = k(x, x) - 2k(x, y) + k(y, y)$. Continuity of $k$ is part of
universality in Theorem 5 of Gretton et al.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Theorem 5.
