# Optimality of base-stock policies

Consider a finite-horizon periodic-review inventory problem with full backlogging, zero lead time, no setup cost and no disposal: in period $k$, from stock $x$ one orders up to $y \ge x$ at unit cost $c \ge 0$, then independent demand $w_k$ with finite mean occurs, and the cost $L(y - w_k)$ with $L(z) = c_B(-z)^+ + c_Hz^+$ is charged, where $c_B > c$, $c_H \ge 0$ and $c + c_H > 0$; a convex nonnegative terminal cost is charged on the final stock. Assume that for every period $k$ and every $y$ the expectations $E|L(y - w_k)|$ and $E|J_{k+1}(y - w_k)|$ are finite (finite mean demand alone is not enough: a demand with finite mean and infinite variance makes a quadratic terminal cost have infinite expectation). Then each $G_k(y) = cy + E[L(y - w_k) + J_{k+1}(y - w_k)]$ is convex and coercive, so it attains its minimum at some $S_k$, and the base-stock rule $y = \max(x, S_k)$ is optimal in every period; the optimal cost-to-go functions $J_k$ are convex and nonnegative.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- If $h$ is convex then $y \mapsto E[h(y - w)]$ is convex for integrable $w$ with $E|h(y - w)| < \infty$.

## Sources

- J. Le Ny, *Dynamic programming*, lecture 3 "Inventory control", Polytechnique Montréal, 2009, §3.2, Lemmas 3.2.1–3.2.2, <http://www.profs.polymtl.ca/jerome.le-ny/teaching/DP_fall09/notes/lec3_inventoryControl.pdf>
