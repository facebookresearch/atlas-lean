# Matrix product as a sum of permuted entrywise products

For $d\ge1$ and $d\times d$ matrices over a commutative ring, $AB=\sum_{k=0}^{d-1}(\phi^k\circ\sigma(A))\odot(\psi^k\circ\tau(B))$, where $\sigma(A)_{i,j}=A_{i,i+j}$, $\tau(B)_{i,j}=B_{i+j,j}$, $\phi$ shifts columns and $\psi$ shifts rows. It underlies encrypted matrix multiplication with one ciphertext per matrix.

With indices modulo $d$, define $\sigma(A)_{i,j}=A_{i,i+j}$, $\tau(A)_{i,j}=A_{i+j,j}$, $\phi(A)_{i,j}=A_{i,j+1}$ and $\psi(A)_{i,j}=A_{i+1,j}$, and let $\odot$ be the entrywise product. Then

$$
A\cdot B=\sum_{k=0}^{d-1}\big(\phi^k\circ\sigma(A)\big)\odot\big(\psi^k\circ\tau(B)\big).
$$

Under the row-major encoding $\iota(A)[d\,i+j]=A_{i,j}$ into $d^2$ slots, each of $\sigma,\tau,\phi^k,\psi^k$ is a slot permutation. The source evaluates them by the [diagonal method](diagonal-matrix-vector-product.md), counting $2d-1$ nonzero diagonals for $\sigma$ ($d\ge2$), $d$ for $\tau$, two for $\phi^k$ and one for $\psi^k$ ($1\le k<d$), and obtains in a scheme with $d^2$ slots, rotations, constant multiplication and ciphertext multiplication an encrypted product from one ciphertext per input matrix with $O(d)$ operations and depth one ciphertext multiplication plus two constant multiplications.

## Depends on

None.

## Proof depends on

None.

## Expansion

Entry $(i,j)$ of the $k$-th term is $A_{i,i+j+k}B_{i+j+k,j}$; summing over $k$ and substituting $l=i+j+k$ gives $(AB)_{i,j}$. The homomorphic cost claim is the source's Algorithm 2 and Table 1; as a theorem it would need pages for packed ciphertext multiplication with relinearization and rotations in the scheme used (the source uses an approximate scheme).

## Sources

- Xiaoqian Jiang, Miran Kim, Kristin Lauter, Yongsoo Song, "Secure Outsourced Matrix Computation and Application to Neural Networks", ACM CCS 2018, DOI 10.1145/3243734.3243837, §3.1 (Equation 2), §3.3, Tables 1–2 and Algorithm 2.
