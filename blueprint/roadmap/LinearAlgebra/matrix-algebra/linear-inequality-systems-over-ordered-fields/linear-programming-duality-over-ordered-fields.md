# Linear-programming duality over linearly ordered fields

Over a linearly ordered field $K$, consider the primal program $\max\{c^{T}x: Ax\le b\}$ and the dual $\min\{y^{T}b: y\ge0,\ y^{T}A=c^{T}\}$. Weak duality holds: $c^{T}x\le y^{T}b$ for all feasible $x,y$. If both are feasible, both optima are attained and equal. If the primal is feasible and the dual is infeasible, the primal is unbounded, and symmetrically.

## Proof sketch

Weak duality is $c^{T}x=y^{T}Ax\le y^{T}b$. For strong duality, apply Farkas' lemma to the combined system $Ax\le b$, $-A^{T}y\le-c$, $A^{T}y\le c$, $-y\le0$, $c^{T}x\ge b^{T}y$ and show the alternative contradicts feasibility of both programs; a solution of the combined system gives optimal $x, y$ with equal values by weak duality. If the dual is infeasible, Farkas' lemma gives $z$ with $Az \le 0$ and $c^{T}z > 0$, along which the primal is unbounded.

## Proof depends on

- [Farkas' lemma over linearly ordered fields](farkas-lemma-over-ordered-fields.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- Jiří Matoušek, Bernd Gärtner, "Understanding and Using Linear Programming", Springer, 2007.
