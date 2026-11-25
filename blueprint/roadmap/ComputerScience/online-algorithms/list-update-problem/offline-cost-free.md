# Offline cost with free exchanges

Given lists $L_0, L_1, L_2, \dots$, target indices
$J_0, J_1, J_2, \dots$ and a request sequence $\sigma = x_0 x_1 \cdots x_{m-1}$, let $L_t'$ be the
list obtained from $L_t$ by the free exchange that moves $x_t$ forward to index $J_t$ (counting
from $0$); it equals $L_t$ if $x_t$ already has index at most $J_t$. The offline cost with free
exchanges of $\sigma$ is the sum over $t < m$ of the access cost of $x_t$ in $L_t$ (its position,
counting from $1$) plus the number of inversions between $L_t'$ and $L_{t+1}$.

This is the model of Sleator and Tarjan: the free exchange costs nothing, and each pair of items
whose relative order changes from $L_t'$ to $L_{t+1}$ costs one. With no free moves it is the
offline cost without free exchanges.
