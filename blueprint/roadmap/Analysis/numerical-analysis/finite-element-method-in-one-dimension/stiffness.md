# Assembled stiffness matrix of the P1 method

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with element lengths $h_i$ and [element
vectors](element-vector.md) $e_i$. The stiffness matrix is the $(n+1) \times (n+1)$ matrix

$$K = \sum_{i=0}^{n-1} \frac{1}{h_i}\, e_i e_i^{\mathsf T}:$$

each element contributes $\frac{1}{h_i} \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$ at the nodes
$i, i + 1$.
