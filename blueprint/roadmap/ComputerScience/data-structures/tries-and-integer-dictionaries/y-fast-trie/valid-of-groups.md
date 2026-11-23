# Assembling a valid grouped y-fast trie from groups

Let $w$ and $B$ be natural numbers
and let $g_1, \dots, g_k$ be a list of groups, each a list of keys in $\{0, \dots, 2^w - 1\}$.
Suppose every group is nonempty, has at most $B$ keys, and is strictly increasing, and the
groups are ordered: every key of an earlier group is smaller than every key of a later group.
Then the grouped y-fast trie with group bound $B$ assembled from these groups, whose
representatives are the last elements of the groups, is valid.
