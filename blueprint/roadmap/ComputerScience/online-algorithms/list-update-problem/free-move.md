# Free move

A free exchange (Sleator and Tarjan): right after accessing $x$ in a list $L$,
move $x$ forward to index $j$ (indices counted from $0$), at no charge. If the index of $x$ in
$L$ is at most $j$, the list is unchanged, so $x$ never moves backward for free; otherwise the
result is obtained by erasing the first occurrence of $x$ from $L$ and inserting $x$ back so that
it has index $j$.
