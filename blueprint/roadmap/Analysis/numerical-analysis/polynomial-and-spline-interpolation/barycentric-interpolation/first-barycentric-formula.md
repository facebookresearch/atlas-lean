# First barycentric formula

Let $F$ be a field, $s$ a finite set of indices, $v : s \to F$ the nodes and $r : s \to F$ the values, let $p = \sum_{i \in s} r_i L_i$ be the Lagrange interpolant with the Lagrange basis polynomials $L_i$ of the nodes, let $\ell(x) = \prod_{i \in s}(x - v_i)$ be the node polynomial and $w_i$ the [barycentric weights](barycentric-weights.md). Then for every $x \in F$ that is not a node

$$p(x) = \ell(x) \sum_{i \in s} \frac{w_i}{x - v_i}\, r_i .$$

For distinct real nodes $p$ is the polynomial of degree at most $|s| - 1$ with $p(v_i) = r_i$.

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the derivation of (3.3) from the Lagrange formula (2.1). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
