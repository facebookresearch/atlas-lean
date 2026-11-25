# Six divisor-function identities from the power recursion lemma

Let $n \ge 1$ be a
natural number. Write $\sigma(m)$ for the sum of the positive divisors of $m$,
$\bar\sigma_3(m) = \sum_{d \mid m,\ m/d \text{ odd}} d^3$,
$\tilde\sigma_3(m) = \sum_{d \mid m} (-1)^{d-1} d^3$ and $S(m) = \sigma(m) - 4\sigma(m/4)$, where
$\sigma(m/4) = 0$ unless $4 \mid m$; all of these are $0$ at every integer $m \le 0$. Then
$2n\,\sigma(2n+1) = \sum_{j=1}^{n} (5j(j+1) - 2n)\,\sigma(2n+1-j(j+1))$; the number
$n\,S(n) - 2\sum_{j=1}^{n} (5j^2 - n)\,S(n-j^2)$ is $n$ if $n$ is a perfect square and $0$
otherwise;
$n\,\bar\sigma_3(n+1) = \sum_{j=1}^{n+1} (9j(j+1)/2 - n)\,\bar\sigma_3(n+1-j(j+1)/2)$; the
number $n\,\tilde\sigma_3(n) - 2\sum_{j=1}^{n} (-1)^j (9j^2 - n)\,\tilde\sigma_3(n-j^2)$ is
$(-1)^{n-1} n$ if $n$ is a perfect square and $0$ otherwise;
$\sum_{j=0}^{n+1} (3j - n)\,\sigma(2j+1)\,\bar\sigma_3(n+1-j) = 0$; and
$n\,(\tilde\sigma_3(n) + (-1)^n S(n)) =
8\sum_{j=1}^{n-1} (3j - n)(-1)^j S(j)\,\tilde\sigma_3(n-j)$.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 19 (`jis-2024-24.1.6-thm-19`).
