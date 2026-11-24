# Profile shape score at a common size factor

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For a real $a$, the profile shape score is

$$S_p(a) = \sum_{i \in \iota} \psi_{k_i}(a) - n \bigl(\log(a + M) - \log a\bigr),$$

with the [digamma increment](digamma-increment.md) $\psi_k(a) = \sum_{j < k} 1/(a + j)$, the
[sample mean](count-mean.md) $M$ and the real logarithm ($\log 0 = 0$, $\log x = \log |x|$ for
$x < 0$). It does not involve a size factor. For $a > 0$, a common size factor $\sigma > 0$ and
$M > 0$ it is the [shape score along the rate root](shape-score-const-rate-root.md)
$\hat b(a) = \sigma a / M$.
