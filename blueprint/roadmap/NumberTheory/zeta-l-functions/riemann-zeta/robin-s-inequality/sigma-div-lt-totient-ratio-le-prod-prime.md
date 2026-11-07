# Bounds for $\sigma(n)/n$ over primes avoiding $p_j$

For $\ell \ge 1$ let $p_\ell$ be the
$\ell$-th prime, so that $p_1 = 2$. Let $1 \le j \le k$, let $q_1 < \cdots < q_k$ be primes
different from $p_j$, let $\alpha_1, \dots, \alpha_k \ge 1$, and put
$n = \prod_{i=1}^k q_i^{\alpha_i}$. Let $\sigma(n)$ be the sum of the divisors of $n$ and let
$\varphi$ be Euler's totient function. Then

$$
\frac{\sigma(n)}{n} < \prod_{i=1}^k \frac{q_i}{q_i - 1} = \frac{n}{\varphi(n)} \le
\prod_{1 \le \ell \le k + 1,\ \ell \ne j} \frac{p_\ell}{p_\ell - 1}.
$$

The paper prints the last inequality as strict; it is an equality when the $q_i$ are exactly the
first $k$ primes other than $p_j$ (for example $j = k = 1$ and $n = 3$, where both sides are
$3/2$), and the proof ($p_i \le q_i$) gives $\le$.

## Sources

- Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 1 (`integers-2026-A86-lem-1`).
