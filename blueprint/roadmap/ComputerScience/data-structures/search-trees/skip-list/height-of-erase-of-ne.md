# Erasure preserves the heights of other keys

If $S$ is a valid skip list and $k$, $k'$
are keys with $k' \ne k$, then the stored tower height of $k'$ in the skip list obtained by
erasing $k$ from $S$ is the same as in $S$; in particular $k'$ has no stored height in one exactly
when it has none in the other.
