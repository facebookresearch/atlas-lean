# Existence and uniqueness of the natural cubic spline

Let $a = t_0 < t_1 < \cdots < t_n = b$, $n \ge 1$, and let $y_0, \dots, y_n$ be real numbers. Then there is exactly one [natural cubic spline](natural-cubic-spline.md) $s$ with knots $t_0, \dots, t_n$ and $s(t_i) = y_i$ for every $i$.

With $h_i = t_{i+1} - t_i$ and $z_i = s''(t_i)$, a cubic spline is determined on each interval by $y_i, y_{i+1}, z_i, z_{i+1}$, and the continuity of $s'$ at the interior knots is the linear system

$$\frac{h_{i-1}}{6} z_{i-1} + \frac{h_{i-1} + h_i}{3} z_i + \frac{h_i}{6} z_{i+1} = \frac{y_{i+1} - y_i}{h_i} - \frac{y_i - y_{i-1}}{h_{i-1}}, \qquad 1 \le i \le n - 1.$$

With $z_0 = z_n = 0$ its matrix is tridiagonal and strictly diagonally dominant, hence nonsingular (in Mathlib as [det_ne_zero_of_sum_row_lt_diag](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L63 "det_ne_zero_of_sum_row_lt_diag")).

## Depends on

- [Natural cubic spline](natural-cubic-spline.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.10.1, the derivation of $s_i$ from (3.55), the system (3.56) with the natural end conditions (3.57), and the remark that its matrix is strictly diagonally dominant and therefore invertible. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
