# Transposed partition in Stanley coordinates

For tuples $\mathbf{m} = (m_1, \dots, m_r)$
and $\mathbf{n} = (n_1, \dots, n_r)$ of natural numbers, the transpose
$\rho(\mathbf{m}, \mathbf{n})$ is the pair of tuples
$((n_1 + \dots + n_r, \dots, n_1 + n_2, n_1), (m_r, m_{r-1} - m_r, \dots, m_1 - m_2))$: for
$1 \le j \le r$, the $j$-th entry of the first tuple is $n_1 + \dots + n_{r+1-j}$ and the $j$-th
entry of the second tuple is $m_{r+1-j} - m_{r+2-j}$, where $m_{r+1} := 0$ and subtraction of
natural numbers is truncated at $0$.

On a partition with $m_1 > \dots > m_r$ this reflects its Young diagram in the main diagonal.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Section 4, transposed partition in Stanley coordinates.
