# Barycentric weights

For distinct real nodes $x_0, \dots, x_n$, let $\ell(x) = (x - x_0)(x - x_1)\cdots(x - x_n)$ be the node polynomial. The *barycentric weights* are

$$w_j = \frac{1}{\prod_{k \ne j} (x_j - x_k)} = \frac{1}{\ell'(x_j)}, \qquad j = 0, \dots, n .$$

They depend only on the nodes, cost $O(n^2)$ operations, and a new node $x_{n+1}$ updates them in $O(n)$ operations. Multiplying all weights by a common nonzero factor does not change the [second barycentric formula](second-barycentric-formula.md).

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the node polynomial (3.1) and the weights (3.2), the update of the weights, and Section 5, the identity (5.2). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
