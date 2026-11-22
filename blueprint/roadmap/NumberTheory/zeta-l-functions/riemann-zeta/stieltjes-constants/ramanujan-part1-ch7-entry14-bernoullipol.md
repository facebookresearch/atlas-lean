# Asymptotic expansion of $\sum 1/(n(n^x - 1))$ as $x \to 0^+$

Let $a_0$ be a real number
such that $\sum_{n=2}^{m} \frac{1}{n \log n} - \log \log m$ tends to $a_0$ as $m \to \infty$, and
let $(c_k)_{k \ge 0}$ be real numbers such that, for every $k \ge 0$,
$\sum_{j=1}^{m} (\log j)^k / j - (\log m)^{k+1} / (k+1)$ tends to $c_k$ as $m \to \infty$. Then for
every real $x > 0$ the series $F(x) = \sum_{n \ge 2} \frac{1}{n(n^x - 1)}$ converges absolutely, and
for every $N \ge 0$,

$$F(x) = \frac{a_0 - \log x}{x} + \frac{1 - \gamma}{2}
  + \sum_{k=1}^{N} \frac{B_{2k}\, c_{2k-1}}{(2k)!} x^{2k-1} + O(x^{2N+1})
  \quad (x \to 0^+),$$

where $\gamma$ is Euler's constant and $B_{2k}$ are the Bernoulli numbers.

Proof: Truncated Laurent expansion of the exponential kernel, an exact partial-sum identity,
and a sum-versus-integral error bound, followed by passage to the defining limits.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
