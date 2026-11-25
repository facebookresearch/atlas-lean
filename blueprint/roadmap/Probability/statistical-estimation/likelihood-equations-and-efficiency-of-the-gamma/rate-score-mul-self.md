# The log-rate score is the rate times the rate score

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For every real $a$, every $b > 0$ and positive size factors $s_i > 0$, the
[rate score](rate-score.md) $S_b(a, b) = \sum_i \bigl(a/b - (a + k_i)/(b + s_i)\bigr)$ and the
[log-rate score](rate-score-log.md)
$\tilde S_b(a, b) = \sum_i \bigl(a - (a + k_i)\, b/(b + s_i)\bigr)$ satisfy

$$S_b(a, b)\, b = \tilde S_b(a, b).$$
