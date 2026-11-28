# Points of the primal-dual central path

$(x, y, s)$ satisfies the central-path equations with parameter $\nu$ for the linear program
$\min c^\top x$, $Ax = b$, $x \ge 0$ and its dual $\max b^\top y$, $A^\top y + s = c$, $s \ge 0$:
$x_i s_i = \nu$ for every $i$, $Ax = b$, $A^\top y + s = c$, $x > 0$ and $s > 0$. The predicate is just these
equations and inequalities. Only under the [standing assumptions](standing-assumptions.md) and for $\nu > 0$
is there exactly one solution, the point of the central path with parameter $\nu$; without them there may be
none, or (when $A$ has deficient row rank) many choices of $y$.
