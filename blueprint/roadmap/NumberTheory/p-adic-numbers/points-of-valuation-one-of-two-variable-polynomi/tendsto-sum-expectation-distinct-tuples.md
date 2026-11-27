# Sums of expectations over distinct tuples tend to one

Let $f \in \mathbb{Z}[x, y]$ have
partial derivatives $f_x$ and $f_y$, and for a prime $p$ let $C_f(\mathbb{F}_p)$ be the set of
pairs of integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that there is a natural number
$P_0$ such that for every prime $p \ge P_0$ and all integers $x, y$, the integers $f(x, y)$,
$f_x(x, y)$ and $f_y(x, y)$ are not all divisible by $p$; that $|C_f(\mathbb{F}_p)|/p \to 1$ as
$p \to \infty$ through the primes; and that Conjecture 1 holds for $f$. For a tuple $P$ of points
of $C_f(\mathbb{F}_p)$, let $N(P)$ be the number of pairs $(a, b)$ with $0 \le a, b < p$ such that
$p^2 \mid f(r + ap, s + bp)$ for every point $(r, s)$ of $P$. Then for every $k \ge 1$,
$\sum_P N(P)/p^2 \to 1$ as $p \to \infty$ through the primes, where $P$ runs over the $k$-tuples
of pairwise distinct points of $C_f(\mathbb{F}_p)$.

In the paper's notation the sum is $\sum_{l_1 \ne \dots \ne l_k} E[Y_{l_1} \cdots Y_{l_k}]$.
The paper's proof takes $|C_f(\mathbb{F}_p)|/p \to 1$ from the Hasse–Weil bounds, which need an
irreducibility hypothesis the paper does not state; it is assumed directly here.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 5, under the standing assumption of Section 3.
