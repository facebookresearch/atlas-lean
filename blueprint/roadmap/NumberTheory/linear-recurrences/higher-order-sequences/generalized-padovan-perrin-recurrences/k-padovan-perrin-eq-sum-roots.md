# Root formula for the $k$-Padovan–Perrin numbers

Let $k \ge 2$ be an integer, let
$P(z) = z^3 - z - k$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + 3) = v(n + 1) + k\,v(n)$ for every $n$, that is, $v$ solves the Padovan–Perrin recurrence
with $k_1 = 1$, $k_2 = k$, $p = 1$, $s = 2$. Put $A_0 = k\,v(0) + v(1)$, $A_1 = k\,v(1) + v(2)$
and $A_2 = k\,v(2)$. Then for every $n \ge 3$,

$$v(n) = \sum_\lambda \frac{A_0\lambda^{n-1} + A_1\lambda^{n-2} + A_2\lambda^{n-3}}{P'(\lambda)},$$

where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

Since $27 k^2 - 4 \neq 0$, the roots of $P$ are distinct. The paper prints the middle coefficient
as $k\,v(1)$; $k\,v(1) + v(2)$ is the coefficient $A_1$ of its Theorem 3, and the printed form
fails already for $k = 2$, $(v(0), v(1), v(2)) = (0, 0, 1)$, $n = 4$, where it gives $0$ while
$v(4) = 1$.

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Proposition 10.
