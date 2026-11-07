# Poisson limit for points of valuation $> 1$

Let $f \in \mathbb{Z}[x, y]$ have partial
derivatives $f_x$ and $f_y$, and for a prime $p$ let $C_f(\mathbb{F}_p)$ be the set of pairs of
integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that there is a natural number $P_0$
such that for every prime $p \ge P_0$ and all integers $x, y$, the integers $f(x, y)$,
$f_x(x, y)$ and $f_y(x, y)$ are not all divisible by $p$; that $|C_f(\mathbb{F}_p)|/p \to 1$ as
$p \to \infty$ through the primes; and that Conjecture 1 holds for $f$. For $0 \le k, l < p$ let
$X(k, l)$ be the number of points $(x, y)$ of the square
$\{kp, \dots, kp + p - 1\} \times \{lp, \dots, lp + p - 1\}$ with $p^2 \mid f(x, y)$. Then for
every $j \ge 0$,

$$
\frac{\#\{(k, l) : 0 \le k, l < p,\ X(k, l) = j\}}{p^2} \to \frac{e^{-1}}{j!}
$$

as $p \to \infty$ through the primes. That is, for $(k, l)$ uniformly random in
$\{0, \dots, p - 1\}^2$, $X(k, l)$ converges in distribution to a Poisson variable with
parameter $1$ (for $\mathbb{N}$-valued variables, pointwise convergence of the mass functions is
convergence in distribution).

The hypothesis $|C_f(\mathbb{F}_p)|/p \to 1$ is the Hasse–Weil input of the paper's proof,
assumed directly, as in the companion statement about sums over distinct tuples.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Theorem 1 (`integers-2026-A82-thm-1`).
