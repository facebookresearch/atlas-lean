# Element growth in Gaussian elimination with partial pivoting

Let $A$ be a real $n \times n$ matrix. Gaussian elimination with partial pivoting performs, at step $k = 1, \dots, n - 1$, a row exchange that brings into the pivot position $(k, k)$ an entry of largest modulus among the entries $(k, k), \dots, (n, k)$ of the current matrix, and then subtracts multiples of row $k$ from rows $k + 1, \dots, n$ to make their entries in column $k$ zero (no subtraction when the pivot is zero). In exact arithmetic it produces a permutation matrix $P$, a unit lower triangular matrix $L$ and an upper triangular matrix $U$ with

$$PA = LU, \qquad |l_{ij}| \le 1 \ \text{for all } i, j, \qquad \max_i |u_{ij}| \le 2^{n-1} \max_i |a_{ij}| \ \text{for every column } j.$$

The bound on $U$ is what makes the [backward error of Gaussian elimination](exists-add-mul-vec-eq-of-is-fl-lu.md), proportional to $|\hat L|\,|\hat U|$, small relative to $A$ in practice: the worst case $2^{n-1}$ is attained only by rare matrices, and observed growth is far smaller.

## Related topics

- [Backward error of floating-point LU factorization](exists-add-mul-vec-eq-of-is-fl-lu.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 5 (Gaussian elimination, 19 September 2024), the definition of the pivot growth factor and the theorem stated for partial pivoting ("with GEPP, $|L| \le 1$ and $\max(|U(:,i)|) \le 2^{n-1}\max(|A(:,i)|)$") with the remarks after it. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_05.txt>
