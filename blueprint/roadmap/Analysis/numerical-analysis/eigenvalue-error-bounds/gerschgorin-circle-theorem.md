# Gerschgorin's circle theorem

Let $K$ be a normed field, $\iota$ a finite index type and $A = (a_{ij})$ an $\iota \times \iota$ matrix over $K$. Every eigenvalue $\mu$ of $A$ lies in one of the closed balls

$$\{z \in K : \|z - a_{kk}\| \le \textstyle\sum_{j \ne k} \|a_{kj}\|\}, \qquad k \in \iota .$$

For $K = \mathbb{C}$ these are the Gerschgorin discs of $A$.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.4, Theorem 3.11 (Gerschgorin). <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
- Mathlib, `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`: `eigenvalue_mem_ball`.
