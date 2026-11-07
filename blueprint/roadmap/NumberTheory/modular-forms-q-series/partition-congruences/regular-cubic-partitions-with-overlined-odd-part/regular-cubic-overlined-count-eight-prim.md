# Congruences modulo 4 and 8 for 8-regular cubic partitions with odd parts overlined

Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_8(n)$ for the $n$th coefficient of $f_2 f_8^2 f_{32} / (f_1^2 f_4 f_{16})$, the
number of $8$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-3}{p}\right) = -1$, let $s = (p - 1)/6$ if $p \equiv 1 \pmod 6$
and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing coefficients of power
series in $q$,

$$
f_4 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{13p^{2\delta} - 7}{6}\right) q^n \equiv
2 (-1)^{\delta s} f_1 f_8^2 \pmod{4},
$$



$$
f_1 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{19p^{2\delta} - 7}{6}\right) q^n \equiv
4 (-1)^{\delta s} f_2^2 f_{16} \pmod{8},
$$

and for all $n \ge 0$ and $1 \le t \le p - 1$,

$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{13p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{4},
$$



$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{19p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{8}.
$$

The divisions by $6$ are exact. With $\psi(q) = f_2^2 / f_1$ and $\psi(q^4) = f_8^2 / f_4$, the
power series congruences are the paper's $\sum_n a_8(\ldots) q^n \equiv 2 (-1)^{\delta s} f_1
\psi(q^4) \pmod{4}$ and $\sum_n a_8(\ldots) q^n \equiv 4 (-1)^{\delta s} \psi(q) f_{16} \pmod{8}$,
multiplied by $f_4$ and by $f_1$.

## Sources

- Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 11, eqs. (93)–(96) (`integers-2024-A101-thm-11`).
