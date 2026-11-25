# Most significant digit

For natural numbers $b$ and $m$, let $k$ be the base-$b$
logarithm of $m$ rounded down, that is, the largest $k$ with $b^k \le m$ when $b \ge 2$ and
$m \ge 1$, and $k = 0$ otherwise. The most significant digit of $m$ in base $b$ is
$\lfloor m / b^k \rfloor$. When $b \ge 2$ and $m \ge 1$ this is the leading digit of the
base-$b$ expansion of $m$.
