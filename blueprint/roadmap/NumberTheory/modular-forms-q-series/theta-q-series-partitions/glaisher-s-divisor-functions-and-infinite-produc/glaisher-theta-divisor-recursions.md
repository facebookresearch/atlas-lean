# Six recursions for Glaisher's divisor functions from the theta functions

Let $n \ge 1$
be a natural number. Write $\sigma(m)$ for the sum of the positive divisors of $m$, $d_D(m)$ for
the sum of the divisors $d$ of $m$ with $m/d$ odd, $d_F(m) = \sum_{d \mid m} (-1)^{d-1} d$,
$\bar\sigma_3(m) = \sum_{d \mid m,\ m/d \text{ odd}} d^3$,
$\tilde\sigma_3(m) = \sum_{d \mid m} (-1)^{d-1} d^3$ and $S(m) = \sigma(m) - 4\sigma(m/4)$, where
$\sigma(m/4) = 0$ unless $4 \mid m$; all of these are $0$ at every integer $m \le 0$. Then
$d_D(n) + 2\sum_{j=1}^{n} (-1)^j d_D(n-j^2)$ is $(-1)^{n-1} n$ if $n$ is a perfect square and
$0$ otherwise; $\sum_{j=0}^{n} d_F(n-j(j+1)/2)$ is $n$ if $n = k(k+1)/2$ for some natural number
$k$ and $0$ otherwise; $8\sum_{j=1}^{n-1} (-1)^{j+1} d_D(j)\,S(n-j) = n\,S(n) + (-1)^n d_D(n)$;
$4\sum_{j=1}^{n} d_F(j)\,\sigma(2n+1-2j) = n\,\sigma(2n+1)$;
$16\sum_{j=1}^{n-1} d_D(j)\,\tilde\sigma_3(n-j) = d_D(n) - n\,\tilde\sigma_3(n)$; and
$8\sum_{j=1}^{n} d_F(j)\,\bar\sigma_3(n+1-j) = n\,\bar\sigma_3(n+1)$.

These recursions come from the theta functions $\varphi(q) = \sum_{k \in \mathbb{Z}} q^{k^2}$ and
$\psi(q) = \sum_{k \ge 0} q^{k(k+1)/2}$.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 14 (`jis-2024-24.1.6-thm-14`).
