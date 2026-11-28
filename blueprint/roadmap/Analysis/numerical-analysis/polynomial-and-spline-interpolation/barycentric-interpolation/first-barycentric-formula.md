# First barycentric formula

Let $F$ be a field, $s$ a finite set of indices, $v$ the nodes and $r$ the values, let $L_i = \prod_{j \in s,\ j \ne i} (v_i - v_j)^{-1}(X - v_j)$ be the Lagrange basis polynomials, with $0^{-1} = 0$, and let $p = \sum_{i \in s} r_i L_i$ be this basis sum (Mathlib's `Lagrange.interpolate`), which is defined even when nodes repeat. Let $\ell(x) = \prod_{i \in s}(x - v_i)$ be the node polynomial and $w_i$ the [barycentric weights](barycentric-weights.md). Then for every $x \in F$ that is not a node

$$p(x) = \ell(x) \sum_{i \in s} \frac{w_i}{x - v_i}\, r_i .$$

No distinctness of the nodes is assumed. When the nodes of $s$ are distinct, $p$ is the polynomial of degree at most $|s| - 1$ with $p(v_i) = r_i$; when two nodes coincide, $p$ need not interpolate: for two indices with both nodes $0$ and values $1, 2$, both basis polynomials and both weights are $0$, so $p = 0$.

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 3, the derivation of (3.3) from the Lagrange formula (2.1). <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
