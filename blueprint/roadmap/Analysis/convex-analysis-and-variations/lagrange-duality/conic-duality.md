# Weak duality and strong duality for conic programs

Let $E$ and $F$ be finite-dimensional real inner-product spaces, $K$ a closed convex cone in $E$, $K^* = \{y : \langle y, x\rangle \ge 0 \ \forall x \in K\}$ its dual cone, $A : E \to F$ linear with adjoint $A^*$, $b \in F$ and $c \in E$. For the primal $\min\{\langle c, x\rangle : Ax = b,\ x \in K\}$ and the dual $\max\{\langle b, y\rangle : c - A^*y \in K^*\}$, every primal feasible $x$ and dual feasible $y$ satisfy $\langle b, y\rangle \le \langle c, x\rangle$. If the primal value is finite and some feasible $x$ lies in the interior of $K$, the dual optimum is attained and equals the primal value. The nonnegative orthant gives linear programming and the cone of positive semidefinite matrices in the space of real symmetric matrices, with the trace inner product $\langle X, Y\rangle = \operatorname{tr}(XY)$, gives semidefinite programming. The sufficient second-order condition for a strict local minimum is a separate statement.

## Proof depends on

- [Weak duality](dual-value-le-primal-value.md): weak duality.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.9.1 (generalized inequalities: weak duality and Slater's condition)
