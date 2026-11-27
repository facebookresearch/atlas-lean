# The Fenwick update writes at the visited endpoints

For any Fenwick tree $t$ over an
additive commutative monoid, zero-indexed array position $i$, increment $δ$, and natural
stored index $j$, reading index $j$ (with default $0$) after the update gives its old value
plus $δ$ if $j$ belongs to the update visit list for size $t.\mathrm{size}$ and start $i+1$,
and its old value otherwise. This holds for every stored array, including an empty array,
without a representation invariant. The list is the one over which the implementation folds;
each visited index is in bounds and the dummy entry is never visited. If $i\ge t.\mathrm{size}$
the list is empty.
