# Capacity after deletion

Let $T$ be a dynamic table with capacity $m$ and item count $n$,
and apply deletion to $T$. If $n = 0$, the capacity stays $m$. If $n \ge 1$ and $4(n-1) < m$, the
new capacity is $\lfloor m/2 \rfloor$. Otherwise the capacity stays $m$.
