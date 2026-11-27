# Natural cubic spline

Let $a = t_0 < t_1 < \cdots < t_n = b$, $n \ge 1$, and let $y_0, \dots, y_n$ be real numbers. A *cubic spline* with knots $t_0, \dots, t_n$ that interpolates the data $y_i$ is a function $s : [a, b] \to \mathbb{R}$ such that

- on each interval $[t_i, t_{i+1}]$, $s$ agrees with a polynomial $s_i$ of degree at most $3$;
- $s(t_i) = y_i$ for $0 \le i \le n$;
- $s$, $s'$ and $s''$ are continuous on $[a, b]$, that is $s_{i-1}(t_i) = s_i(t_i)$, $s_{i-1}'(t_i) = s_i'(t_i)$ and $s_{i-1}''(t_i) = s_i''(t_i)$ for $1 \le i \le n - 1$.

It is a *natural* cubic spline if in addition $s''(a) = s''(b) = 0$.

The interpolation and smoothness conditions are $4n - 2$ linear equations for the $4n$ coefficients of $s_0, \dots, s_{n-1}$; the two natural end conditions fix the remaining freedom.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.10.1, the definition of a cubic spline with conditions (3.52)–(3.54), the count of equations that follows, and the natural end conditions (3.57). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
