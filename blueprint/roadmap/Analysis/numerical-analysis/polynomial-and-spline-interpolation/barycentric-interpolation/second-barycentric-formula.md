# Second barycentric formula

Let $x_0, \dots, x_n$ be distinct nodes with [barycentric weights](barycentric-weights.md) $w_j$, and let $p$ be the polynomial of degree at most $n$ with $p(x_j) = f_j$ for all $j$. Then for every $x$ that is not a node

$$p(x) = \frac{\displaystyle\sum_{j=0}^n \frac{w_j}{x - x_j}\, f_j}{\displaystyle\sum_{j=0}^n \frac{w_j}{x - x_j}} .$$

It follows from the [first barycentric formula](first-barycentric-formula.md) applied to $f_j$ and to the constant data $1$, whose interpolant is $1 = \ell(x) \sum_j w_j/(x - x_j)$. Common factors of the weights cancel, and for any nonzero weights the right-hand side is a rational function that still takes the value $f_j$ at $x_j$.

## Depends on

- [Barycentric weights](barycentric-weights.md)

## Proof depends on

- [First barycentric formula](first-barycentric-formula.md)

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 4, the identity (4.1) and the formula (4.2), and Section 9.2, the remark that (4.2) interpolates for an arbitrary set of weights. <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
