# Reading a linear program off a solution of Dantzig's game

Let $(y, x, t)$ be a solution of Dantzig's game for $(A, b, c)$ over a linearly ordered field. Then:

1. $t\,(y^{\mathsf T} b - c^{\mathsf T} x) = 0$;
2. if $t > 0$, then $x/t$ is an optimal solution of the primal $\min\{c^{\mathsf T}x : Ax \ge b, x \ge 0\}$ and $y/t$ is an optimal solution of the dual;
3. if $c^{\mathsf T} x < y^{\mathsf T} b$, then the primal or the dual is infeasible.

A solution with $t = 0$ and $c^{\mathsf T} x = y^{\mathsf T} b$ determines nothing: there is a single strategy of this kind that solves the Dantzig games of two programs, one with an optimal solution and one infeasible.

## Proof sketch

Item 1 multiplies the solution inequalities by $y$, $x$ and $t$ and uses skew-symmetry ($z^{\mathsf T}Pz = 0$) to force equality throughout. If $t > 0$, the scaled vectors are feasible and weak duality with $c^{\mathsf T}x \le y^{\mathsf T}b$ makes both optimal. If $c^{\mathsf T}x < y^{\mathsf T}b$ then $t = 0$, and $x$, $y$ are rays certifying, by a Farkas-type argument, that one of the two programs is infeasible.

## Depends on

- [Dantzig's symmetric game of a linear program](dantzig-game.md)

## Proof depends on

- [Every symmetric zero-sum game has a solution](every-symmetric-game-has-a-solution.md)
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
- George B. Dantzig, "A proof of the equivalence of the programming problem and the game problem", in T. C. Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley, 1951.
