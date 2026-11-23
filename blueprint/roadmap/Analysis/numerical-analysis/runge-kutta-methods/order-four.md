# Order-four conditions

An explicit Runge–Kutta method with Butcher tableau $a$, weights
$b$ and nodes $c$ satisfies the order-four conditions when it satisfies the order-three
conditions, namely $\sum_i b_i = 1$, $\sum_i b_i c_i = 1/2$, $\sum_i b_i c_i^2 = 1/3$ and
$\sum_{i,j} b_i a_{ij} c_j = 1/6$, together with $\sum_i b_i c_i^3 = 1/4$,
$\sum_{i,j} b_i c_i a_{ij} c_j = 1/8$, $\sum_{i,j} b_i a_{ij} c_j^2 = 1/12$ and
$\sum_{i,j,k} b_i a_{ij} a_{jk} c_k = 1/24$. These are the eight Butcher conditions.
