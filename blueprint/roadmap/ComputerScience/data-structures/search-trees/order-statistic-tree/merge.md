# Merging order-statistic trees

The merge of order-statistic trees $A$ and $B$ is defined by
recursion on $A$. If $A$ is empty, it is $B$. If $A$ has root key $x$, left subtree $L$ and right
subtree $R$, it is the node with key $x$, left subtree $L$ and right subtree the merge of $R$ and
$B$, whose cached size is the sum of the cached root sizes of its children plus one, an empty
child counting as zero. Thus $B$ is attached below the rightmost path of $A$, and every node on
that path gets a recomputed cache.

The merge is intended for trees in which every key of $A$ is smaller than every key of $B$, but it
is defined for all pairs of trees.
