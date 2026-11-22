# Goodman's bound on the number of triangles

A finite simple graph with $n$ vertices, $m$ edges and $T$ triangles ($3$-cliques) satisfies

$$m(4m - n^2) \le 3nT,$$

as an inequality of integers. In particular a graph with more than $n^2/4$ edges has a triangle.

The bound is due to A. W. Goodman. Dividing by $n^4/6$ turns it into the inequality $t(K_3) \ge t(K_2)(2t(K_2) - 1)$ between the homomorphism densities $t(K_2) = 2m/n^2$ and $t(K_3) = 6T/n^3$. Razborov derives its limit form $K_3 \ge \rho(2\rho - 1)$ in the flag algebra of graphs and attributes it to Goodman.

The proof counts [ordered triangles](ordered-triangles.md), which are [six per triangle](card-ordered-triangles-eq-six-mul.md), and applies [Goodman's bound in homomorphism-count form](goodman-ordered-triangles.md).

## Sources

- A. W. Goodman, On sets of acquaintances and strangers at any party, Amer. Math. Monthly 66 (1959), 778-783.
- A. A. Razborov, Flag algebras, J. Symbolic Logic 72 (2007), 1239-1282; Example 11 in the author's version, people.cs.uchicago.edu/~razborov/files/flag.pdf.
