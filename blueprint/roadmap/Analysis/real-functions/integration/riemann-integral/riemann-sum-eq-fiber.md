# Riemann sum regrouped over a refinement

Let $f : \mathbb{R} \to \mathbb{R}$, let $T$ be
a tagged partition of $[a, b]$ with points $x_0 < \dots < x_n$ and tags
$\xi_0, \dots, \xi_{n-1}$, and let $T'$ be a tagged partition of $[a, b]$ with points
$x'_0 < \dots < x'_{n'}$, together with tagged-refinement data from $T$ to $T'$ assigning to
each $j < n'$ an index $\sigma(j) < n$. Then the Riemann sum $S_f(T)$ of $f$ over $T$ satisfies

$$S_f(T) = \sum_{j=0}^{n'-1} f(\xi_{\sigma(j)}) \, (x'_{j+1} - x'_j).$$
