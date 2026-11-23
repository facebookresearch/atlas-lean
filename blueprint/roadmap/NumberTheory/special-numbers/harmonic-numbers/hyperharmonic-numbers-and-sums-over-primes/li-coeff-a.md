# Li's coefficients $a(r, m, j)$

The rational numbers $a(r, m, j)$, for natural numbers
$r$, $m$, $j$, are defined by recursion on $r$. For all $m$ and $j$, $a(0, m, j) = 0$; moreover
$a(1, 0, 0) = 1$ and $a(1, m, j) = 0$ for $(m, j) \ne (0, 0)$. For $r \ge 1$ the values of
order $r + 1$ are as follows. First,

$$a(r+1, r, 0) = -\sum_{m=0}^{r-1} \frac{a(r, m, r-m-1)}{r-m}.$$

For $0 \le m \le r - 1$ and $1 \le \ell \le r - m$,

$$a(r+1,m,\ell) = \sum_{j=\ell-1}^{r-1-m} \frac{a(r,m,j)}{j+1} \binom{j+1}{j-\ell+1} B_{j-\ell+1}.$$

For $0 \le m \le r - 1$,

$$a(r+1, m, 0) = -\sum_{y=0}^{m} \sum_{j=\max(0, m-y-1)}^{r-1-y} a(r, y, j)\, D(m, j, y),$$

where

$$D(m, j, y) = \frac{1}{j+1} \sum_{\ell=\max(0, m-y-1)}^{j} \binom{j+1}{j-\ell} B_{j-\ell}
\binom{\ell+1}{m-y} (-1)^{1+\ell-m+y}.$$

All other values $a(r+1, m, \ell)$ are $0$. Here $B_n$ are the Bernoulli numbers with
$B_1 = 1/2$, that is, the numbers determined by $\sum_{j=0}^{k} \binom{k+1}{j} B_j = k + 1$ for
all $k \ge 0$.

Li writes $D(r, m, j, y)$; the value does not depend on $r$.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Lemma 3 (quoting Li, *Euler sums of generalized hyperharmonic numbers*).
