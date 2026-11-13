# Asymptotics of hyperbolic floor sums

Let $r \ge 2$ and let $\tau_r(n)$ be the number of
ordered factorizations $n = n_1 \cdots n_r$ of $n$ into $r$ positive factors. Let
$P(t) = \sum_j a_j t^j$ be a real polynomial with
$\sum_{1 \le n \le x} \tau_r(n) - x P(\log x) = O(x^{1 - 1/r} (\log x)^{r-2})$ as $x \to \infty$.
Let $f$ be a nonnegative real function on the natural numbers such that, for some real $\alpha$
with $0 \le \alpha < 1$, $f(n) = O(n^\alpha)$ as $n \to \infty$, and, for some real $\beta \ge 0$,
$\sum_{1 \le n \le x} f(n) = O(x (\log \log x)^\beta)$ as $x \to \infty$. For $i \ge 0$ let

$$C_i = \sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right).$$

Then, as $x \to \infty$,

$$\sum_{1 \le n \le x} f(\lfloor x/n \rfloor) \, \tau_r(n) = x \sum_{j=0}^{r-1} \sum_{i=0}^{j}
\binom{j}{i} (-1)^i a_j C_i (\log x)^{j-i} + O(x (\log x)^{r-2} (\log \log x)^\beta).$$

The hypothesis $f \ge 0$ is not in the source: its proof bounds the error sum
$\sum_{d \le x} f(d) \, O((x/d)^{1-1/r} (\log (x/d))^{r-2})$ through $\sum_{n \le x} f(n)$,
which controls it only for nonnegative $f$.

## Sources

- Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37, Theorem 1.
