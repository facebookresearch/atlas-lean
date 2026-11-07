# Common lifts of two points with independent gradients

Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $(r_1, s_1)$ and
$(r_2, s_2)$ be pairs of integers in $\{0, \dots, p - 1\}$ with $p \mid f(r_i, s_i)$ for
$i = 1, 2$ and

$$
p \nmid f_x(r_1, s_1) f_y(r_2, s_2) - f_y(r_1, s_1) f_x(r_2, s_2).
$$

Write $F_i(k, l) = f(r_i + kp, s_i + lp)$. Among the pairs $(k, l)$ with $0 \le k, l < p$,
exactly $(p - 1)^2$ have $p \mid F_i(k, l)$ and $p^2 \nmid F_i(k, l)$ for both $i$, exactly
$p - 1$ have $p^2 \mid F_1(k, l)$, $p \mid F_2(k, l)$ and $p^2 \nmid F_2(k, l)$, and exactly
one has $p^2 \mid F_1(k, l)$ and $p^2 \mid F_2(k, l)$.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 3 (`integers-2026-A82-prop-3`).
