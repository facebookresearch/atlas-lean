# Power sums of cyclic numbers

Let $k \ge 1$ be an integer. Let $c_n$ be the $n$-th cyclic
number ($c_1 = 1$), let $C(x)$ be the number of cyclic numbers $m \le x$, and let $\gamma$ be the
Euler–Mascheroni constant. Then, as $n \to \infty$ through the natural numbers,

$$
\sum_{i=1}^{n} c_i^k \sim \frac{n c_n^k}{k+1}
\sim \frac{n^{k+1} e^{k\gamma} (\log \log \log n)^k}{k+1},
$$

and, as $x \to \infty$ through the real numbers,

$$
\sum_{m \le x,\ m \text{ cyclic}} m^k \sim \frac{C(x)\, c_{C(x)}^k}{k+1}
\sim \frac{C(x)\, x^k}{k+1}
\sim \frac{x^{k+1}}{(k+1) e^{\gamma} \log \log \log x}
\left(1 - \frac{\gamma}{\log \log \log x}\right).
$$

## Sources

- Joel E. Cohen, *Conjectures about Primes and Cyclic Numbers*, Journal of Integer Sequences 28 (2025), Article 25.4.7, Theorem 1 (`jis-2025-25.4.7-thm-1`).
