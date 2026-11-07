# Vertices of the interior hull of a standard clean parallelogram

Let $1 \le a < n$ with
$\gcd(a, n) = 1$, let $P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, and let
$n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, with $m \ge 2$.
Write $A_i / B_i$ for its $i$-th convergent, and put $v_{-1} = (0, 1)$, $v_i = (B_i, A_i)$ for
$i \ge 0$, $u_i = v_i + (1, 0)$ (so $u_{-1} = (1, 1)$) and $w = (a + 1, n)$. Then the vertices of
the convex hull of the lattice points in the interior of $P_{a,n}$ are exactly $u_{-1}$ and
$w - u_{-1}$, the points $u_i$ and $w - u_i$ for odd $i$ with $0 \le i < m$, and the points $v_i$
and $w - v_i$ for even $i$ with $0 \le i < m$.

## Sources

- Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10, Theorem 6 (`integers-2026-A10-thm-6`).
