# Best response condition

`(x, y)` is a Nash equilibrium iff every pure strategy used by
either player is a pure best response to the other's.

For a bimatrix game $(A, B)$ with the row player receiving $x^{\mathsf T} A y$ and the column player $x^{\mathsf T} B y$, $(x, y)$ is a [Nash equilibrium](is-bimatrix-nash.md) if and only if $x_k > 0$ implies $(Ay)_k = \max_l (Ay)_l$ and $y_k > 0$ implies $(B^{\mathsf T} x)_k = \max_l (B^{\mathsf T} x)_l$.
