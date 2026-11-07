# Deletion from a dynamic table

Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$,
each empty or holding an item, and item count $n \le m$. Deleting the last item of $T$ gives the
following table. If $n = 0$, the result is $T$ itself. Otherwise, if $4(n-1) < m$, that is, the
load factor after deletion is strictly below $1/4$, the table contracts: the result has slots
$s_0, \dots, s_{n-2}$ followed by $\lfloor m/2 \rfloor - (n-1)$ empty slots, so capacity
$\lfloor m/2 \rfloor$, and item count $n-1$. Otherwise the result has the slots of $T$ with
$s_{n-1}$ made empty, and item count $n-1$.
