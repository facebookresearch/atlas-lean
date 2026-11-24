# Longest-common-prefix lengths of adjacent suffixes

For a list $s$ and a list of indices
$i_0, i_1, \dots, i_k$, this is the list of length $k$ whose $t$-th entry, for $t < k$, is the
length of the longest common prefix of the suffixes of $s$ starting at $i_t$ and at $i_{t+1}$,
where the suffix starting at an index at or past the end of $s$ is the empty list. It has one
entry per adjacent pair of indices, and it is empty for an empty index list.
