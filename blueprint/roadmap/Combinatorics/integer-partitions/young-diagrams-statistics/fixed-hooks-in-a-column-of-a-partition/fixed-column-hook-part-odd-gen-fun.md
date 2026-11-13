# Odd partitions with a fixed hook in a given column arising from an odd part

Let $n$, $m$
and $k$ be natural numbers with $1 \le m \le k$ and $k$ odd, and let $h$ be an integer with
$h \le k - m$. Count the partitions $\lambda$ of $n$ into odd parts that have an $h$-fixed hook in
column $m$ at some row $s$ with $\lambda_s = k$. Write $(q^2;q^2)_j = \prod_{i\lt j} (1 - q^{2i+2})$
and $(q;q^2)_j = \prod_{i\lt j} (1 - q^{2i+1})$, write $\binom{a}{b}_{q^2}$ for the Gaussian binomial
coefficient in $q^2$, and put $s_t = k - h - m + 1 + t$ for $t \ge 0$. If $m$ is odd, the count is
the coefficient of $q^n$ in

$$\sum_{t=0}^{n} \frac{q^{s_t(k+m)+m(m+h-k-1)}}{(q^2;q^2)_{s_t-1}\,(q;q^2)_{(m-1)/2}}
\binom{t+(k-m)/2}{t}_{q^2},$$

and if $m$ is even, it is the coefficient of $q^n$ in

$$\sum_{t=0}^{n} \frac{q^{s_t(k+m+1)+(m+1)(h-k)+m^2-1}}{(q^2;q^2)_{s_t-1}\,(q;q^2)_{m/2}}
\binom{t+(k-m-1)/2}{t}_{q^2}.$$

Here $s_t \ge 1$, the exponents are positive, and the halves $(k-m)/2$ and $(k-m-1)/2$ are
integers. The $t$-th term has no monomial below $q^t$, so the count is also the coefficient of
$q^n$ in the full series over all $s = s_t \ge k - h - m + 1$; in the paper's notation the bottom
index of the Gaussian binomial is $j = s + h - k + m - 1 = t$.

Corrected reading: as printed, the Gaussian binomials are $\binom{s+h-k+(k-m)/2}{s+h-k}_{q^2}$ and
the even-$m$ exponent is $s(k+m+1)+m(h-k+m)+h-k+1$, which is larger by $2$. Both are slips in
reindexing $k + m - 1 \mapsto k$ the $m = 1$ formula in the paper's proof (its binomial index
$s + h - k$ becomes $s + h - k + m - 1$, and its displayed even-$m$ exponent simplifies to the
one stated here). As printed the statement is false: for $m = k = 3$, $h = 0$, the partition
$(3)$ of $3$ has the $0$-fixed hook $h_{1,3} = 1$, but the printed series has no $q^3$ term (its
first term is $q^{15}$); for $m = 2$, $k = 3$, $h = 0$ the count for $n = 6$ is $1$ and the
printed series has no $q^6$ term.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 8, corrected per its proof.
