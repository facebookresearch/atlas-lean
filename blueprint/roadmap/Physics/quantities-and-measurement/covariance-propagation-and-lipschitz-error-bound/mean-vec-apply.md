# Coordinates of the weighted mean vector are weighted sums

For a finite set $\Omega$, real weights $p : \Omega \to \mathbb{R}$, a map
$X : \Omega \to \mathbb{R}^n$ and a coordinate $i$, coordinate $i$ of the
[weighted mean vector](mean-vec.md) $\bar X$ of $X$ is the weighted expectation of the coordinate
$X_i$:

$$\bar X_i = E_p[X_i] = \sum_{\omega \in \Omega} p(\omega)\, X_i(\omega) .$$

This holds for all real weights, by the definition of $\bar X$; it is an expectation in the
probabilistic sense when $p \ge 0$ and $\sum_\omega p(\omega) = 1$.
