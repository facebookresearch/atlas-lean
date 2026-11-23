# Analytic core of Poisson convergence

Let $\lambda \ge 0$ be a real number, let
$k : \mathbb{N} \to \mathbb{N}$, and for each $n$ let $p_{n,i}$, $0 \le i < k(n)$, be real
numbers. Suppose that $p_{n,i} \ge 0$ for all $n$ and $i$, that for every $\varepsilon > 0$
we have $p_{n,i} < \varepsilon$ for all $i < k(n)$ once $n$ is large enough, and that
$\sum_{i < k(n)} p_{n,i} \to \lambda$ as $n \to \infty$. Then for every natural number $j$,
as $n \to \infty$ the Poisson-binomial mass

$$\sum_{|A| = j} \prod_{i \in A} p_{n,i} \prod_{i \notin A} (1 - p_{n,i})$$

tends to $e^{-\lambda} \lambda^j / j!$, where $A$ runs over the $j$-element subsets of
$\{0, \dots, k(n) - 1\}$ and $i \notin A$ ranges over the elements of that set not in $A$.

Without the hypothesis $p_{n,i} \ge 0$ the conclusion can fail.
