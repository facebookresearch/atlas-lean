# Real Jordan form

For $a \in \mathbb{R}$ let $J_k(a)$ be the $k \times k$ [Jordan block](jordan-block.md) with eigenvalue $a$, and for $a, b \in \mathbb{R}$ with $b > 0$ let $RJ_k(a, b)$ be the real $2k \times 2k$ block matrix whose diagonal $2 \times 2$ blocks are $\begin{pmatrix} a & -b \\ b & a \end{pmatrix}$, whose blocks just above the diagonal are the $2 \times 2$ identity, and whose other blocks are zero. If $T$ is a linear operator on a finite-dimensional real vector space $V$, then $V$ has a basis in which the matrix of $T$ is block diagonal with blocks of the forms $J_k(a)$ and $RJ_k(a, b)$; with $b > 0$ in every block $RJ_k(a, b)$, so that each pair of conjugate complex Jordan blocks $J_k(a + ib)$, $J_k(a - ib)$ gives one real block $RJ_k(a, b)$, the number of blocks of each form and size is determined by the dimensions of the kernels of the powers of $T - a$ and of $(T - a)^2 + b^2$. Consequently two real matrices that are similar over $\mathbb{C}$ are similar over $\mathbb{R}$.

## Depends on

- [Jordan block](jordan-block.md)

## Proof depends on

- [Jordan normal form](exists-jordan-normal-form-of-splits.md)

## Sources

- J. Labute, "The real Jordan canonical form and the rational canonical form", course notes for MATH 251, McGill University, <https://math.mcgill.ca/labute/courses/251.04/jordan3.pdf>, the theorem on the real Jordan canonical form and Corollary 1.
