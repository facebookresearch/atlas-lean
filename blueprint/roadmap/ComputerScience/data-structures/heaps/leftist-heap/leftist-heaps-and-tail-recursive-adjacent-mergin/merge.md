# Merge of leftist heaps

Over a linear order, the merge of two leftist heaps $h_1$ and $h_2$ is their auxiliary merge with
fuel equal to the size of $h_1$ plus the size of $h_2$. This fuel never runs out: each recursive
step removes one node from the pair of heaps still to be merged.
