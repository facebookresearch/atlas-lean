# Toggle order

For a natural number $n$, the toggle order on $n$ points is the list of all
arcs $(i, i + d)$ with $d \ge 1$, $i \ge 0$ and $i + d \le n - 1$, ordered by length
$d = 1, \dots, n - 1$ and, for each length, by increasing left endpoint $i$. In $1$-indexed form it
is $(1,2), (2,3), \dots, (n-1,n), (1,3), \dots, (n-2,n), \dots, (1,n)$.
