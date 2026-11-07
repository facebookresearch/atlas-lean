# Common lifts of two points with dependent gradients

Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $(r_1, s_1)$ and
$(r_2, s_2)$ be pairs of integers in $\{0, \dots, p - 1\}$ with $p \mid f(r_i, s_i)$ for
$i = 1, 2$. Write $a_i = f_x(r_i, s_i)$, $b_i = f_y(r_i, s_i)$ and $c_i = f(r_i, s_i)/p$.
Suppose that for each $i$ the integers $a_i$ and $b_i$ are not both divisible by $p$, and that
$p \mid a_1 b_2 - b_1 a_2$. Write $F_i(k, l) = f(r_i + kp, s_i + lp)$, and among the pairs
$(k, l)$ with $0 \le k, l < p$ let $n_1$ be the number with $p \mid F_i(k, l)$ and
$p^2 \nmid F_i(k, l)$ for both $i$, let $n_2$ be the number with $p^2 \mid F_1(k, l)$,
$p \mid F_2(k, l)$ and $p^2 \nmid F_2(k, l)$, and let $n_3$ be the number with
$p^2 \mid F_1(k, l)$ and $p^2 \mid F_2(k, l)$. If $p$ divides both $a_1 c_2 - c_1 a_2$ and
$b_1 c_2 - c_1 b_2$ (the matrix with rows $(a_i, b_i, c_i)$ has rank $1$ modulo $p$), then
$n_1 = p(p - 1)$, $n_2 = 0$ and $n_3 = p$. Otherwise (rank $2$) $n_1 = p(p - 2)$, $n_2 = p$
and $n_3 = 0$.

The source assumes only that $f$ has no zero modulo $p^2$ at which $f_x \equiv f_y \equiv 0
\pmod p$ and that one column is non-zero. The counts need both gradients $(a_i, b_i)$ non-zero
modulo $p$, which the paper's Case 2 uses. Without this they fail for $f = -x^2 + y^2 - x - 1$,
$p = 3$, $(r_1, s_1) = (0, 1)$, $(r_2, s_2) = (1, 0)$: the gradient vanishes at $(1, 0)$, the
rank is $2$, and $(n_1, n_2, n_3) = (6, 3, 0)$ rather than $(3, 3, 0)$.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 4 (`integers-2026-A82-prop-4`).
