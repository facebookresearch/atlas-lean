# The classical RK4 tableau satisfies all eight order-four conditions

The classical fourth-order Runge–Kutta tableau, with $a_{21} = a_{32} = 1/2$, $a_{43} = 1$, the
other $a_{ij}$ zero, weights $b = (1/6, 1/3, 1/3, 1/6)$ and nodes $c_i = \sum_j a_{ij}$, satisfies
the eight order conditions up to order four: $\sum_i b_i = 1$, $\sum_i b_i c_i = 1/2$,
$\sum_i b_i c_i^2 = 1/3$, $\sum_{i,j} b_i a_{ij} c_j = 1/6$, $\sum_i b_i c_i^3 = 1/4$,
$\sum_{i,j} b_i c_i a_{ij} c_j = 1/8$, $\sum_{i,j} b_i a_{ij} c_j^2 = 1/12$ and
$\sum_{i,j,k} b_i a_{ij} a_{jk} c_k = 1/24$.

## Sources

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I: Nonstiff
  Problems*, 2nd ed., Springer, 1993, Chapter II.
