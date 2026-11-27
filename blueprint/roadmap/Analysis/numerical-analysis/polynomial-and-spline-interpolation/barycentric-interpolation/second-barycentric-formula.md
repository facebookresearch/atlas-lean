# Second barycentric formula

Let $F$ be a field, $s$ a finite set of indices, $v : s \to F$ nodes that are pairwise distinct and $r : s \to F$ the values, let $p = \sum_{i \in s} r_i L_i$ be the Lagrange interpolant and $w_i$ the [barycentric weights](barycentric-weights.md). Then for every $x \in F$ that is not a node

$$p(x) = \frac{\displaystyle\sum_{i \in s} \frac{w_i}{x - v_i}\, r_i}{\displaystyle\sum_{i \in s} \frac{w_i}{x - v_i}} .$$

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 4, the identity (4.1) and the formula (4.2). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
