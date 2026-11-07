# Coefficient vectors from Chan's matrix

Let $(m_{i,j})_{i,j \ge 1}$ be Chan's matrix, and
for $i, j \ge 1$ let $a_{i,j} = m_{4i-3,i+j-1}$ and $b_{i,j} = m_{4i-1,i+j-1}$ be the entries of
the infinite matrices $A$ and $B$. The coefficient vectors
$X_\alpha = (x_{\alpha,1}, x_{\alpha,2}, \dots)$ of integers, for $\alpha \ge 0$, are defined by
$X_0 = (1, 0, 0, \dots)$ and, for $j \ge 1$, $x_{\alpha+1,j} = \sum_{i=1}^{3^\alpha} x_{\alpha,i}
a_{i,j}$ if $\alpha$ is even and $x_{\alpha+1,j} = \sum_{i=1}^{3^\alpha} x_{\alpha,i} b_{i,j}$ if
$\alpha$ is odd.

Since Chan's matrix is lower triangular, row $i$ of $A$ or $B$ vanishes beyond column $3i$, so by
induction $x_{\alpha,i} = 0$ for $i > 3^\alpha$; hence $X_{\alpha+1} = X_\alpha A$ for even
$\alpha$ and $X_{\alpha+1} = X_\alpha B$ for odd $\alpha$.

The formalization indexes the vectors from $0$: its value at $(\alpha, i)$ is $x_{\alpha,i+1}$.

## Sources

- Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2, equations (3)-(4), and Theorem 8.
