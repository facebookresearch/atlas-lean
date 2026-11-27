# How often $\varphi(\sigma(n)) \ge n / f(n)$

Write $\log_k$ for the $k$-fold iterated
natural logarithm, so $\log_3 x = \log \log \log x$, and let $\varphi$ be Euler's totient function
and $\sigma$ the sum of divisors. Let $f$ be a real function that is positive and non-decreasing
on $(0, \infty)$ with $f(x) = o(\log_4 x)$ as $x \to \infty$, and let $P_f(x)$ be the number of
integers $n$ with $1 \le n \le x$ and $\varphi(\sigma(n)) \ge n / f(n)$. Then, as $x \to \infty$,

$$
P_f(x) = O\left(\frac{x f(x)}{\log_4 x} +
\frac{x \log_3 x}{(\log x)^{1/\log_3 x} \log_4 x}\right)
$$

and $P_f(x) = o(x)$.

## Sources

- Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*, INTEGERS 24 (2024), Article A65, Theorem 2.
