# Exact formula for the length-three run count

For a natural number $B$, let $A_B(3)$ be
the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $3$, and for integers
$m \ge 1$ let $d_B(m) = 2\lfloor B/m \rfloor + 1$. Then

$$A_B(3) = \sum_{x, y} \left(d_B(|x|)\, d_B(|y|)\, d_B(|x+y|) - 1\right),$$

where the sum runs over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$ and
$x + y \ne 0$, and also

$$
A_B(3) = 2 \sum_{m=1}^{B} \sum_{n=1}^{B} d_B(m)\, d_B(n)\, d_B(m+n) +
4 \sum_{1 \le n < m \le B} d_B(m)\, d_B(n)\, d_B(m-n) - (4B^2 - 2B).
$$

## Sources

- Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6 (`integers-2026-A122-prop-6`).
