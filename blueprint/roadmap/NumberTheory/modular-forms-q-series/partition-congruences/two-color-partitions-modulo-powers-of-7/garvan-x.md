# Garvan's coefficient vectors

Let $(m_{i,j})$ be Garvan's matrix. Garvan's coefficient
vectors $x_k = (x_{k,1}, x_{k,2}, \dots)$ for $k \ge 1$ are defined by $x_{1,1} = 7$,
$x_{1,2} = 7^2$ and $x_{1,i} = 0$ for $i \ge 3$, and, for $k \ge 1$ and $i \ge 1$, by

$$x_{k+1,i} = \sum_{j=1}^{7^k} x_{k,j}\, m_{4j,j+i}$$

if $k$ is odd and

$$x_{k+1,i} = \sum_{j=1}^{7^k} x_{k,j}\, m_{4j+1,j+i}$$

if $k$ is even. Values at index $0$ are conventions outside the source's range.

The source sums over all $j \ge 1$; the cut at $7^k$ loses nothing, since $m_{i,j} = 0$ for
$j > 2i$, so the largest index of a nonzero entry of $x_{k+1}$ is at most $7$ times that of
$x_k$ plus $2$, which stays below $7^{k+1}$.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Section 1.
