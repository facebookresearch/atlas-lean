# Generalized hyperharmonic numbers

For natural numbers $n$ and $k$ and a complex number
$r$, the generalized hyperharmonic number $H_n^{[r]}(k)$ is $0$ when $k > n$; when $k \le n$ it is
the elementary symmetric polynomial of degree $n - k$ in $r, r + 1, \ldots, r + n - 1$ divided by
$n!$, that is,

$$H_n^{[r]}(k) = \frac{1}{n!} \sum_{0 \le j_1 < \cdots < j_{n-k} < n} \prod_{i=1}^{n-k} (r + j_i).$$

The source defines $H_n^{[r]}(k)$ in (2.4) by $(-1)^k k! \, H_n^{[r]}(k) = D_x^k \binom{n+r-x-1}{n}$
at $x = 0$, where $D_x^k$ is the $k$-th derivative in $x$; the explicit form above follows from it.
For $r = 1$ it is the depth-$k$ multiple harmonic number, and for
$r \notin \{0, -1, \ldots, 1 - n\}$ it equals
$\binom{n+r-1}{n} \sum_{1 \le i_1 < \cdots < i_k \le n} \prod_{j=1}^{k} 1/(i_j + r - 1)$,
see (2.10).

## Sources

- Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*, INTEGERS 26 (2026), Article A81, Section 2, (2.4) and (2.10) (`integers-2026-A81-cor-1`).
