# Huffman loop with an accumulated lookup count

The loop takes a fuel $n$, a next serial
number $s$, a binary min-heap $H$ of Huffman priorities, ordered lexicographically by weight and
then serial number, a table $T$ whose cells each hold at most one work item, and a counter $c$.
Taking serial $i$ from a table succeeds when cell $i$ holds a work item whose priority has serial
number $i$, and returns that item's tree together with the table with cell $i$ emptied. With fuel
$0$, the loop extracts the minimum $p$ of $H$, leaving a heap $H'$, and takes the serial number of
$p$ from $T$, obtaining a tree $t$ and a table $T'$; it returns $(t, c + 1)$ if $H'$ is empty and
no cell of $T'$ holds a work item, and fails otherwise. With fuel $n + 1$, it extracts the minimum
$p_1 = (w_1, s_1)$ of $H$ and then the minimum $p_2 = (w_2, s_2)$ of the remaining heap, leaving a
heap $H'$; it takes $s_1$ from $T$ and then $s_2$ from the resulting table, obtaining trees $t_1$,
$t_2$ and a table $T'$. It then runs with fuel $n$, next serial number $s + 1$, the heap $H'$ with
the priority $p = (w_1 + w_2, s)$ inserted, the table $T'$ with a new last cell holding the work
item of priority $p$ whose tree has left subtree $t_1$ and right subtree $t_2$, and counter
$c + 2$. If any extraction or take fails, the loop fails.

The counter thus grows by one for each work item taken from the table. The Huffman loop with
lookup count is the case $c = 0$.
