# Congruences modulo 16 for 8-regular cubic partitions with odd parts overlined

Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_8(n)$ for the $n$th coefficient of $f_2 f_8^2 f_{32} / (f_1^2 f_4 f_{16})$, the
number of $8$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-6}{p}\right) = -1$, let $s = (p - 1)/6$ if $p \equiv 1 \pmod 6$
and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing coefficients of power
series in $q$,

$$
f_8 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{25p^{2\delta} - 7}{6}\right) q^n \equiv
8 (-1)^{\delta s} f_1 f_{16}^2 \pmod{16},
$$

and for all $n \ge 0$ and $1 \le t \le p - 1$,

$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{25p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{16}.
$$

The divisions by $6$ are exact. With $\psi(q^8) = f_{16}^2 / f_8$, the first congruence is
the paper's $\sum_n a_8(\ldots) q^n \equiv 8 (-1)^{\delta s} f_1 \psi(q^8) \pmod{16}$
multiplied by $f_8$.

## Sources

- Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 12, eqs. (105), (106) (`integers-2024-A101-thm-12`).
