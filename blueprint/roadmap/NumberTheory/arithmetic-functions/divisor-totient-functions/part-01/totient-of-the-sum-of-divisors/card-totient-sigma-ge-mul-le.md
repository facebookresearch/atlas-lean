# Upper bound for the number of $n$ with $\varphi(\sigma(n)) \ge c n$

Write $\log_k$ for
the $k$-fold iterated natural logarithm, so $\log_3 x = \log \log \log x$, and let $\varphi$ be
Euler's totient function and $\sigma$ the sum of divisors. For every real $c > 0$ there is a
constant $C$ such that for all sufficiently large $x$, the number of integers $n$ with
$1 \le n \le x$ and $\varphi(\sigma(n)) \ge c n$ is at most

$$
\frac{\pi^2 x}{6 c \log_4 x} +
C \, \frac{x \log_3 x}{(\log x)^{1/\log_3 x} \log_4 x}.
$$

The bound is only claimed for large $x$ since it needs $\log_4 x > 0$, that is, $x > e^{e^e}$.

## Sources

- Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*, INTEGERS 24 (2024), Article A65, Theorem 1 (`integers-2024-A65-thm-1`).
