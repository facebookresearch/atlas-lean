# Coefficient vectors for even powers of 7

Let $(m_{i,j})$ be Garvan's matrix and
$x_k$ Garvan's coefficient vectors, and fix $k \ge 1$. The coefficient vectors
$y^{(2k)}_\beta = (y^{(2k)}_{\beta,1}, y^{(2k)}_{\beta,2}, \dots)$ of Theorem 3, $\beta \ge 1$,
are defined by $y^{(2k)}_{1,j} = x_{2k-1,j}$ and, for $\beta \ge 1$,

$$y^{(2k)}_{\beta+1,j} = \sum_{i=1}^{7^{2k+\beta-2}} y^{(2k)}_{\beta,i}\, m_{4i,i+j}$$

if $\beta$ is odd and

$$y^{(2k)}_{\beta+1,j} = \sum_{i=1}^{7^{2k+\beta-2}} y^{(2k)}_{\beta,i}\, m_{4i+2,i+j}$$

if $\beta$ is even. The definition also assigns conventional values for $k = 0$ and
$\beta = 0$.

The source sums over all $i \ge 1$; the cut at $7^{2k+\beta-2}$ lies above the support of
$y^{(2k)}_\beta$, since each step maps the largest index $s$ of a nonzero entry to at most
$7s + 4$.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Theorem 3.
