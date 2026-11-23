# Extract-min in an indexed minimum queue

Costs are counted as five event counts:
comparisons, swaps, reads of the position vector, writes to the position vector, and entry
appends, pops or replacements. Given an indexed minimum queue $q$, extract-min fails (returns
nothing) exactly when the heap of $q$ is empty, at zero cost. Otherwise let $(k, v)$ be the root
entry of the heap. If the heap has one entry, extract-min returns $(k, v)$ together with the
queue whose heap is empty and in which $v$ has no position, at the cost of one position write
and one entry pop. If the heap has at least two entries, the root is swapped with the last entry
and the positions of both are updated, the last slot is removed, the position of $v$ is cleared,
and the new root is sifted down: while it has a child, let $c$ be its smaller child (the left
one on ties); if $c$ is smaller than it, the two are swapped and the positions of both are
updated, otherwise the sift stops. It returns $(k, v)$ together with the resulting queue, at the
cost of one swap, three position writes and one entry pop, plus, at each sift-down step, one
comparison between the two children when both exist, one comparison with $c$, and one swap and
two position writes when a swap is made.
