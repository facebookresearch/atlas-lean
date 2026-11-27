# Dantzig's symmetric game of a linear program

For $A \in K^{m \times n}$, $b \in K^m$, $c \in K^n$ over a linearly ordered field $K$, consider the primal program $\min\{c^{\mathsf T}x : Ax \ge b,\ x \ge 0\}$ and its dual $\max\{y^{\mathsf T} b : y^{\mathsf T}A \le c^{\mathsf T},\ y \ge 0\}$. *Dantzig's game* is the symmetric game with the $(m+n+1) \times (m+n+1)$ skew-symmetric payoff matrix

$$
P = \begin{pmatrix} 0 & A & -b \\ -A^{\mathsf T} & 0 & c \\ b^{\mathsf T} & -c^{\mathsf T} & 0 \end{pmatrix}.
$$

A mixed strategy $(y, x, t)$ solves it exactly when $tb \le Ax$, $y^{\mathsf T}A \le t c^{\mathsf T}$ and $c^{\mathsf T}x \le y^{\mathsf T} b$.

## Depends on

- [Symmetric zero-sum game and its solutions](symmetric-zero-sum-game.md)
- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- George B. Dantzig, "A proof of the equivalence of the programming problem and the game problem", in T. C. Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley, 1951.
- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
