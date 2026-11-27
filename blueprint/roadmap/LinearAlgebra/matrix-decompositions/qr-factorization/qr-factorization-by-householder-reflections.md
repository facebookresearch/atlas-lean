# QR factorization by Householder reflections

Let $A$ be a real $m \times n$ matrix with $m \ge n$. Then there are Householder reflections $H_1, \dots, H_s$, $s = \min(m - 1, n)$, each of the form $\begin{pmatrix} I_{i-1} & 0 \\ 0 & I - 2u_i u_i^{\mathsf T} \end{pmatrix}$ with $u_i \in \mathbb{R}^{m-i+1}$ a unit vector or $H_i = I$, such that

$$H_s \cdots H_2 H_1 A = R$$

is upper triangular. So $A = QR$ with the orthogonal $m \times m$ matrix $Q = H_1 H_2 \cdots H_s$. The $i$-th step chooses $u_i$ so that the reflection maps the subcolumn $A(i{:}m, i)$ of the current matrix to a multiple of the first unit vector, and applying it to the trailing $(m - i + 1) \times (n - i + 1)$ submatrix costs about $4(m - i + 1)(n - i + 1)$ floating-point operations. The whole factorization, with $Q$ kept implicitly as the vectors $u_i$, therefore costs about $\sum_i 4(m - i + 1)(n - i + 1) \approx 2n^2 m - \tfrac23 n^3$ operations, and the method is backward stable.

## Depends on

- [A Householder reflection maps a vector to a multiple of the first unit vector](householder-reflection-maps-a-vector-to-a-multiple-of-e1.md)

## Related topics

- [Existence of the reduced QR factorization](exists-qr.md): the Gram–Schmidt construction for matrices with independent columns.

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 7 (least squares, 4 October 2024), the algorithm for the QR decomposition of an $m \times n$ matrix, $m \ge n$, by Householder transformations, the cost $\sum_{i=1}^n 4(m - i + 1)(n - i + 1) \approx 2n^2 m - \tfrac23 n^3$ of its trailing updates, to leading order, and the overview of QR algorithms at the start of the lecture (Householder QR is stable). <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_07.txt>
