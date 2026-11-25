# Grouped y-fast trie from a sorted list

For a group bound $B$ and a list $l$ of
$w$-bit keys, this is the grouped y-fast trie whose groups, in order, are consecutive pieces of
$l$ that together make up $l$, and whose representative x-fast trie is obtained from the empty
x-fast trie by inserting the last element of each group, in order. If $B > 0$, the groups are
obtained by repeatedly cutting off the first $B$ keys, so every group has exactly $B$ keys
except possibly the last, which has between one and $B$ keys. If $B = 0$, the only group is $l$
itself. In both cases there are no groups when $l$ is empty.

The construction is intended for strictly increasing $l$. It yields a valid trie when $B > 0$
and $l$ is strictly increasing, and an invalid one when $B = 0$ and $l$ is nonempty.
