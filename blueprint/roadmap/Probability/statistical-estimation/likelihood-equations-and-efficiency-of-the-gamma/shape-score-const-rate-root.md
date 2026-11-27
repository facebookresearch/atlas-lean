# Along the rate root the shape score is the profile shape score

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. Let the size factors equal a common value, $s_i = \sigma$ for every $i$, with $\sigma > 0$,
let the [sample mean](count-mean.md) $M$ be positive and let $a > 0$. Then at the rate root
$\hat b(a) = \sigma a / M$ the [shape score](shape-score.md) is the
[profile shape score](profile-shape-score.md)
$S_p(a) = \sum_i \psi_{k_i}(a) - n\bigl(\log(a + M) - \log a\bigr)$: $S_a(a, \hat b(a)) = S_p(a)$.
