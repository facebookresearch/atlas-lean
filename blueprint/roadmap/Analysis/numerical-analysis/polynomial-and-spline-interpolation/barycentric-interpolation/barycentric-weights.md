# Barycentric weights

Let $F$ be a field, $\iota$ a type of indices, $s$ a finite set of indices and $v : \iota \to F$ the nodes. For every index $i \in \iota$, in $s$ or not, the *barycentric weight* (Mathlib's nodal weight) is

$$w_i = \prod_{j \in s,\ j \ne i} (v_i - v_j)^{-1},$$

with the field convention $0^{-1} = 0$. So $w_i = 0$ when another node of $s$ coincides with $v_i$, and for $i \notin s$ the product runs over all of $s$. For distinct real nodes $x_0, \dots, x_n$ and $j \in \{0, \dots, n\}$ this is $w_j = 1/\prod_{k \ne j}(x_j - x_k)$.

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the node polynomial (3.1) and the weights (3.2). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
