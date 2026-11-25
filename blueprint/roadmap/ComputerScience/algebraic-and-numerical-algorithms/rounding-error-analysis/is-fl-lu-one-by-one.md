# Floating-point LU of a $1 \times 1$ matrix

Let $K$ be a field with a linear order and a floor function, $p$ a natural number and $a \in K$. For the $1 \times 1$ matrix $A = (a)$, the matrices $L = (1)$ and $U = (a)$ are the factors computed by [Gaussian elimination without pivoting in $p$-bit floating point](is-fl-lu.md): the only entry of $U$ is $U_{00} = A_{00}$, an empty sum subtracted from the unrounded $A_{00}$, so no rounding occurs, even when $a$ is not a floating-point number.
