# Barycentric weights

Let $F$ be a field, $s$ a finite set of indices and $v : s \to F$ the nodes. The *barycentric weight* (Mathlib's nodal weight) of the node $v_i$, $i \in s$, is

$$w_i = \prod_{j \in s,\ j \ne i} (v_i - v_j)^{-1} .$$

For distinct real nodes $x_0, \dots, x_n$ this is $w_j = 1/\prod_{k \ne j}(x_j - x_k)$.

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the node polynomial (3.1) and the weights (3.2). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
