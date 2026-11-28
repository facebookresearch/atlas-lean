# Summed cell vectors give the at-risk counts

Let $k$ and $r$ be natural numbers and $\Omega$ a set. Let $W_0, W_1, \dots$ be functions $\Omega \to (\{0, \dots, k-1\} \times \{0, \dots, r-1\}) \times \{0, \dots, k-1\}$, and write $W_i(\omega) = ((T_i, J_i), C_i)$. The cell vector of a subject $w = ((T, J), C)$ is the vector indexed by the [cells](../part-01/cell.md) with coordinates

$$v(w)^{E}_{l,c} = \mathbf{1}[\min(T, C) = l,\ T \le C,\ J = c], \qquad v(w)^{R}_{l} = \mathbf{1}[l \le \min(T, C)].$$

For $n \in \mathbb{N}$ and $\omega \in \Omega$, the grouped competing-risks data of the first $n$ subjects have observation times $0, 1, \dots, k-1$, failure counts and censoring counts

$$d_{j,c} = \#\{i < n : \min(T_i, C_i) = j,\ T_i \le C_i,\ J_i = c\}, \qquad w_j = \#\{i < n : \min(T_i, C_i) = j,\ T_i > C_i\}.$$

The number at risk at $j$ in these grouped data is $Y_j = \sum_{l \ge j} \big(\sum_{c} d_{l,c} + w_l\big)$.

For every $n \in \mathbb{N}$, every $\omega \in \Omega$ and every grid index $j$,

$$\Big(\sum_{i=0}^{n-1} v\big(W_i(\omega)\big)\Big)^{R}_{j} = Y_j.$$
