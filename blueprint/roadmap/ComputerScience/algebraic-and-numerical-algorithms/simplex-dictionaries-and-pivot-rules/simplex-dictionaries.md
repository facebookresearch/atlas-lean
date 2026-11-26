# Simplex dictionaries and pivoting

For variables indexed by a finite linearly ordered set and a field $K$, a **dictionary** consists of a set $B$ of basic variables and, for each basic $x_i$, an expression $x_i = \beta_i + \sum_{j \notin B} a_{ij} x_j$, together with an objective $z = z_0 + \sum_{j \notin B} c_j x_j$. Its **solutions** are the assignments satisfying all equations; its **basic solution** sets nonbasic variables to $0$; it is **feasible** if every $\beta_i \ge 0$. A **pivot** on entering variable $x_s$ and leaving variable $x_r$ (with $a_{rs} \ne 0$) solves the $x_r$ equation for $x_s$ and substitutes. Pivoting preserves the solution set and the objective, and a ratio-test pivot preserves feasibility and does not decrease $z_0$. For a feasible dictionary: if no $c_j > 0$ the basic solution is optimal; if some $c_s > 0$ has $a_{is} \ge 0$ for all $i$, the objective is unbounded along a ray.

## Depends on

- [Termination and correctness of the simplex method with Bland's rule](../../graph-algorithms/linear-programming-and-flows/termination-and-correctness-of-the-simplex.md)

## Sources

- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
