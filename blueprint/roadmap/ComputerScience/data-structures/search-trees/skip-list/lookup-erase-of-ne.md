# Erasure preserves lookups of other keys

If $S$ is a valid skip list and $k$, $k'$ are
keys with $k' \ne k$, then looking up $k'$ in the skip list obtained by erasing $k$ from $S$ gives
the same result as looking up $k'$ in $S$: the same value, or no value in both.
