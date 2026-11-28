# Strong linear programming duality

Let $A$ be a real $m \times n$ matrix, and let
$b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$; inequalities between vectors are componentwise.
Suppose some $x \in \mathbb{R}^n$ satisfies $x \ge 0$ and $Ax \le b$, and that $c \cdot x$ is
bounded above over all such $x$. Then there exist $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$
with $x \ge 0$, $Ax \le b$, $y \ge 0$, $A^{\mathsf{T}} y \ge c$ and $c \cdot x = b \cdot y$.

By weak duality, such $x$ and $y$ are optimal solutions of the primal problem of maximizing
$c \cdot x$ subject to $x \ge 0$, $Ax \le b$ and of the dual problem of minimizing $b \cdot y$
subject to $y \ge 0$, $A^{\mathsf{T}} y \ge c$.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.

## Background

- [Weak duality](weak-linear-programming-duality.md): every $x \ge 0$ with $Ax \le b$ and every $y \ge 0$ with $A^{\mathsf{T}} y \ge c$
  satisfy $c \cdot x \le b \cdot y$.
- Linear programming duality is the special case of Lagrange duality for a linear
  objective and linear constraints (Boyd–Vandenberghe §5.2.4); strong duality for linear programs
  needs only feasibility, not Slater's condition.
