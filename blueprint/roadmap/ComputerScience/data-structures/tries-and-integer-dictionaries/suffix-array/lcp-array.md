# The LCP array

For a list $s$ over a linearly ordered alphabet, the LCP array of $s$ is
the list of longest-common-prefix lengths of adjacent suffixes in suffix-array order: if the
suffix array of $s$ is $i_0, i_1, \dots, i_k$, then the LCP array has length $k$ and its $t$-th
entry, for $t < k$, is the length of the longest common prefix of the suffixes of $s$ starting
at $i_t$ and at $i_{t+1}$. It is empty when $s$ is empty.
