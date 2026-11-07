# Basis independence of the rank of a bilinear form

Let $V$ be a vector space over a field
$K$, let $B$ be a bilinear form on $V$, and let $b = (b_i)_{i \in n_1}$ and
$c = (c_j)_{j \in n_2}$ be bases of $V$ indexed by finite types $n_1$ and $n_2$. Then the rank of
$B$ with respect to $b$ equals the rank of the Gram matrix $(B(c_i, c_j))_{i, j \in n_2}$ of $B$
in $c$.

Proof: The Gram matrix in one basis is the Gram matrix in the other multiplied on both sides by
change-of-basis matrices. Since the rank of a product is at most the rank of each factor, each
rank is at most the other, hence they are equal.

## Sources

- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989), Chapter III.
