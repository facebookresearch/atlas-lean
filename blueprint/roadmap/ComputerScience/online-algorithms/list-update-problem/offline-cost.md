# Offline cost without free exchanges

Given lists $L_0, L_1, L_2, \dots$, the offline cost
of a request sequence $\sigma = x_0 x_1 \cdots x_{m-1}$ is the sum over $t < m$ of the access cost
of $x_t$ in $L_t$ (its position, counting from $1$) plus the number of inversions between $L_t$
and $L_{t+1}$. That is, the algorithm serves request $t$ with $L_t$ and then rearranges it into
$L_{t+1}$, paying one for each pair of items whose relative order it changes.

Adding free exchanges gives the offline cost with free exchanges.
