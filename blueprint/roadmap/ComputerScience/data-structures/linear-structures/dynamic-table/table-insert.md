# TABLE-INSERT

Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$ and item count
$n \le m$, and let $x$ be an item. Inserting $x$ into $T$ proceeds as follows. If $m = 0$, first
replace the slots by a single empty slot. Then, if the table is full, that is, $n$ equals the
current capacity $c$, allocate $2c$ empty slots and copy the $c$ old slots into the first $c$ of
them, at cost $1$ per copied slot. Finally write $x$ into slot $n$, at cost $1$, and set the item
count to $n + 1$. The result is the new table together with the total cost.
