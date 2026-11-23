# Formula for the contents of a dynamic table

Let $T$ be a dynamic table with slots
$s_0, \dots, s_{m-1}$, each empty or holding an item, and item count $n \le m$. The contents of
$T$ is the array obtained from the prefix $s_0, \dots, s_{n-1}$ by skipping the empty slots and
keeping the items of the occupied ones, in order.
