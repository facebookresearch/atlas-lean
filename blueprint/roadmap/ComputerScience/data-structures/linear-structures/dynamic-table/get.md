# Lookup in a dynamic table

Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$,
each empty or holding an item, and item count $n \le m$. The lookup at logical position $i$
returns the item held by $s_i$ when $i < n$ and $s_i$ is occupied; it returns no value when
$i < n$ and $s_i$ is empty, and when $i \ge n$.
