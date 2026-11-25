# Evaluating a matrix of polynomials at a matrix

Let $m, n \in \mathbb{N}$, $F = (f_{ij})$ an $m \times m$ matrix whose entries are complex polynomials, and $A$ a complex $n \times n$ matrix. Then $F(A)$ is the $mn \times mn$ complex matrix, with rows and columns indexed by pairs $(i, k) \in \{0, \dots, m-1\} \times \{0, \dots, n-1\}$, given by

$$F(A)_{(i, k), (j, l)} = \big(f_{ij}(A)\big)_{kl},$$

where $f_{ij}(A) = \sum_r a_r A^r$ for $f_{ij}(z) = \sum_r a_r z^r$. Viewed as an $m \times m$ block matrix acting on $\mathbb{C}^m \otimes \mathbb{C}^n$, its $(i, j)$ block is $f_{ij}(A)$.

## Sources

- M. Crouzeix, Numerical range and functional calculus in Hilbert space, *J. Funct. Anal.* 244 (2007), 668–690.
- M. Crouzeix and C. Palencia, The numerical range is a $(1+\sqrt{2})$-spectral set, *SIAM J. Matrix Anal. Appl.* 38 (2017), 649–655.
