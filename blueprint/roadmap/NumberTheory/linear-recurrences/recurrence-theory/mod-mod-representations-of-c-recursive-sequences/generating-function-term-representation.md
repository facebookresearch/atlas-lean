# Term extraction from the generating function persists in larger bases

Let
$t_0, t_1, t_2, \dots$ be natural numbers and let $c$, $m$ and $r$ be natural numbers with
$c \ge 2$, $m \ge 2$ and $c \le r$. Suppose that for every $n \ge m$ the real series
$\sum_{k \ge 0} t_k \, (c^{-n})^k$ is summable and

$$t_n = \Bigl\lfloor c^{n^2} \sum_{k \ge 0} t_k \, (c^{-n})^k \Bigr\rfloor \bmod c^n.$$

Then for every $n \ge m$,

$$t_n = \Bigl\lfloor r^{n^2} \sum_{k \ge 0} t_k \, (r^{-n})^k \Bigr\rfloor \bmod r^n.$$

No summability at $r^{-n}$ is assumed: the hypothesis gives $t_n < c^n \le r^n$ for $n \ge m$,
which makes the series at $r^{-n}$ converge.

## Sources

- M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 3.
