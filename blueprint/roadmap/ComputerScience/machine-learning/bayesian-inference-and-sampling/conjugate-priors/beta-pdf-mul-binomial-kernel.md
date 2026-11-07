# Beta prior times binomial likelihood

Let $a, b > 0$ be real, $n, k$ natural numbers,
$m = n - k$ if $k \le n$ and $m = 0$ otherwise, and $\theta$ real. Write $f_{a,b}$ for the
$\mathrm{Beta}(a, b)$ density (zero outside $(0, 1)$) and $B$ for the beta function. Then the
density $f_{a,b}(\theta)$ times the probability that the binomial kernel at $\theta$ gives exactly
$k$ successes in $n$ trials equals
$\binom{n}{k} \frac{B(a + k, b + m)}{B(a, b)} f_{a + k, b + m}(\theta)$, as an identity in
$[0, \infty]$.
