# Move-to-front against a static list

Let $M$ be a list of distinct items, $L$ a
rearrangement of $M$, and $\sigma$ a sequence of $m$ requests, each an item of $M$. Then the
access cost of move-to-front on $\sigma$ starting from $M$, plus $m$, is at most twice the cost
of serving $\sigma$ with the fixed list $L$ (the sum over the requests of their positions in $L$,
counting from $1$), plus the number of inversions between $M$ and $L$ (the pairs of items that
$M$ and $L$ order differently).
