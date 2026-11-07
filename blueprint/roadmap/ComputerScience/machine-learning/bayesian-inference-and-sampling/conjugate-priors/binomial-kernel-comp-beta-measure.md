# The beta-binomial distribution

Let $a, b > 0$ be real, $n, k$ natural numbers and
$B(x, y) = \Gamma(x)\Gamma(y)/\Gamma(x + y)$ the beta function. Under a $\mathrm{Beta}(a, b)$
prior on the success probability, the marginal probability (the evidence) that the binomial kernel
gives exactly $k$ successes in $n$ trials is $\binom{n}{k} \frac{B(a + k, b + n - k)}{B(a, b)}$,
where $n - k$ is truncated at $0$.
