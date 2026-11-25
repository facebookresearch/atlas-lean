# Volume of the cross-polytope

For every $n \ge 1$, the cross-polytope $\{x \in \mathbb{R}^n : |x_1| + \dots + |x_n| \le 1\}$ has
volume $2^n / n!$.

## Idea

The cross-polytope is the union of $2^n$ copies of the simplex
$\{x_i \ge 0,\ x_1 + \dots + x_n \le 1\}$, one in each orthant, meeting in null sets. Slicing at
$x_n = t$ gives a simplex scaled by $1 - t$, so the volume $v_n$ of the simplex satisfies
$v_n = \int_0^1 (1 - t)^{n-1} v_{n-1}\, dt = v_{n-1} / n$, hence $v_n = 1 / n!$. The cube
$[-1, 1]^n$, of volume $2^n$, and the cross-polytope are polar to each other; the product of their
volumes, $4^n / n!$, is the value in Mahler's conjecture on volume products of symmetric convex
bodies.

## Statements

- [Volume of the cross-polytope](volume-coordinate-cross-polytope.md)
