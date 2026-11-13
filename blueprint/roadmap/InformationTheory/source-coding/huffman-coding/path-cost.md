# Weighted external path length of a Huffman weight tree

For a Huffman weight tree $T$,
write $w(T)$ for its total leaf weight. The weighted external path length $P(T)$ of $T$ is
defined by the merge recurrence: a leaf $T$ has $P(T) = 0$, and a tree $T$ with subtrees $L$
and $R$ has $P(T) = P(L) + P(R) + w(L) + w(R)$.
