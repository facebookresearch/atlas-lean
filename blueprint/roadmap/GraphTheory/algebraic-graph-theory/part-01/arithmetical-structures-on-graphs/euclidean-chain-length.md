# Euclidean chain function

For natural numbers $x_1$ and $x_2$, the Euclidean chain
$x_1, x_2, x_3, \dots$ is given by $x_{i+1} = (-x_{i-1}) \bmod x_i$ (the least nonnegative
residue) while $x_i \ne 0$, and by $x_{i+1} = 0$ once $x_i = 0$. The Euclidean chain function is
defined by the recursion $F(x, 0) = 1$ and $F(x, y) = 1 + F(y, (-x) \bmod y)$ for $y \ne 0$. For
$x_1 > 0$, $F(x_1, x_2)$ is the number of positive terms of the Euclidean chain.

For $x_1 = 0$ the recursion also counts the first term $0$: $F(0, 0) = 1$ and $F(0, 1) = 2$,
although the chains $0, 0$ and $0, 1, 0$ have $0$ and $1$ positive terms.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12 (arXiv numbering).
