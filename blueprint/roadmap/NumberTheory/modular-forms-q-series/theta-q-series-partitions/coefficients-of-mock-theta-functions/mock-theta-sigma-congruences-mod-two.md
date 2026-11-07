# Congruences modulo 2 for the mock theta function $\sigma$

Write
$\sigma(q) = \sum_{n \ge 0} P_\sigma(n) q^n$ for the sixth-order mock theta function $\sigma$ and
let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-2}{p}\right) = -1$ and let $\alpha \ge 0$ be an integer. Then, coefficientwise,

$$
f_3 \sum_{n \ge 0} P_\sigma\Bigl(2 p^{2\alpha} n + \frac{11 p^{2\alpha} + 1}{12}\Bigr) q^n
\equiv f_2 f_6^2 \pmod 2,
$$

and for all integers $n \ge 0$ and all integers $j$ with $1 \le j \le p - 1$,

$$
P_\sigma\Bigl(2 p^{2\alpha+2} n + 2 p^{2\alpha+1} j + \frac{11 p^{2\alpha+2} + 1}{12}\Bigr)
\equiv 0 \pmod 2.
$$

Since $f_2 f_6^2 / f_3 = f_2 \psi(q^3)$ with $\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$, the first
congruence says that the series of $P_\sigma(2 p^{2\alpha} n + (11 p^{2\alpha} + 1)/12)$ is
congruent to $f_2 \psi(q^3)$ modulo $2$. The division by $12$ is exact since
$p^2 \equiv 1 \pmod{24}$.

## Sources

- Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock Theta Functions*, INTEGERS 25 (2025), Article A72, Theorem 6 (`integers-2025-A72-thm-6`).
