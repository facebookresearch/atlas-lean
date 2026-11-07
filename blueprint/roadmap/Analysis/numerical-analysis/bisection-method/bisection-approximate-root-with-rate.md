# Bisection method converges at a linear rate

Let $f : \mathbb{R} \to \mathbb{R}$ be
continuous on $[a, b]$, where $a \le b$ and $f(a) \le 0 \le f(b)$, and let $u, v$ be a bisection
sequence for $f$ from $a$ to $b$. Then there is $c \in [a, b]$ with $f(c) = 0$ such that the
midpoints $(u_n + v_n)/2$ converge to $c$ and $|(u_n + v_n)/2 - c| \le (b - a)/2^{n+1}$ for
every $n \in \mathbb{N}$.

Proof: Monotone convergence gives the common endpoint limit, continuity makes it a root, and the
halved interval length gives the midpoint error bound, following Burden and Faires, Theorem 2.1.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entries `bisection method` and `rate of convergence and estimation of error` (unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Theorem 2.1.
