# The diagonal alignment stays in the band

Let $w, i, j \in \mathbb{N}$ and let $x$, $y$
be lists of lengths $m$ and $n$. If $|i - j| \le w$ and $|(i + m) - (j + n)| \le w$, then the
band check of the diagonal alignment of $x$ and $y$ with width $w$ from offset $(i, j)$ is true.

The match phase keeps the offset difference and the gap phases interpolate it.
