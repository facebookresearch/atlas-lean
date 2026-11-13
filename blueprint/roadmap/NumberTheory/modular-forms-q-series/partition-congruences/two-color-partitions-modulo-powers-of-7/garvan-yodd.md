# Coefficient vectors for odd powers of 7

For $k \ge 1$ and $\beta \ge 1$ the vectors
$y^{(2k-1)}_\beta = (y^{(2k-1)}_{\beta,1}, y^{(2k-1)}_{\beta,2}, \dots)$ are built from Garvan's
vector $x_{2k-1}$ and Garvan's matrix $m_{i,j}$: $y^{(2k-1)}_{1,j} = x_{2k-1,j}$ and

$$y^{(2k-1)}_{\beta+1,j} = \sum_{i=1}^{7^{2k+\beta-2}} y^{(2k-1)}_{\beta,i}\, m_{4i+1,i+j}.$$

The index $\beta = 0$ gives $0$, and for $k = 0$ every entry is $0$.

The sum over $i$ stops at $7^{2k+\beta-2}$, above the support of $y^{(2k-1)}_\beta$ (each step
maps support $s$ into $7s + 2$).

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Theorem 2.
