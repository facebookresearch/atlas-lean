# Hyperbolic floor sums of additive functions of prime exponents

Let $r \ge 2$ and let
$\tau_r(n)$ be the number of ordered factorizations $n = n_1 \cdots n_r$ of $n$ into $r$ positive
factors. Let $P(t) = \sum_j a_j t^j$ be a real polynomial with
$\sum_{1 \le n \le x} \tau_r(n) - x P(\log x) = O(x^{1 - 1/r} (\log x)^{r-2})$ as $x \to \infty$.
Let $g$ be a real function on the natural numbers with $g(1) \ne 0$ and $g(a) = O(2^{a/2})$ as
$a \to \infty$. For $n \ge 1$ let $f(n) = \sum_{p \mid n} g(v_p(n))$, the sum over the primes $p$
dividing $n$, where $v_p(n)$ is the exponent of $p$ in $n$, and for $i \ge 0$ let

$$C_i = \sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right).$$

Then, as $x \to \infty$,

$$\sum_{1 \le n \le x} f(\lfloor x/n \rfloor) \, \tau_r(n) = x \sum_{j=0}^{r-1} \sum_{i=0}^{j}
\binom{j}{i} (-1)^i a_j C_i (\log x)^{j-i} + O(x (\log x)^{r-2} \log \log x).$$

Since $f(n)$ sums only over the primes dividing $n$, the source's convention $g(0) = 0$ is not
needed.

## Sources

- Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37, Proposition 1 (`integers-2026-A37-prop-1`).
