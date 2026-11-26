# The LLL potential

For linearly independent vectors $b_1, \dots, b_n$ in a real inner product space with Gram-Schmidt vectors $b_1^*, \dots, b_n^*$, let $d_i = \det\big(\langle b_j, b_k \rangle\big)_{j,k \le i} = \prod_{j \le i} \|b_j^*\|^2$ be the $i$-th leading Gram determinant. The **LLL potential** is $D = \prod_{i=1}^{n-1} d_i$. A **size-reduction step** replaces $b_i$ by $b_i - r b_j$ for some $j < i$ and $r \in \mathbb{Z}$; an **exchange step** swaps $b_i$ and $b_{i+1}$ when the Lovász condition $\delta\|b_i^*\|^2 \le \|b_{i+1}^* + \mu_{i+1,i} b_i^*\|^2$ fails, where $\mu_{i+1,i}$ is the Gram-Schmidt coefficient.

## Depends on

- [The Lenstra–Lenstra–Lovász algorithm](../lattice-basis-reduction/the-lenstralenstralovasz-algorithm.md)
- [The Q factor of the Gram–Schmidt QR factorization](../../../LinearAlgebra/matrix-decompositions/qr-factorization/qr-q.md)

## Sources

- A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring Polynomials with Rational Coefficients", Mathematische Annalen 261(4), 1982.
