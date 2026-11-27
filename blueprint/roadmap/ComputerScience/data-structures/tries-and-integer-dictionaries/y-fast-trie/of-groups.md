# Grouped y-fast trie from a list of groups

For a list of groups $g_1, \dots, g_k$,
each a list of $w$-bit keys, and any group-size bound $B$, this is the grouped y-fast trie
whose groups are $g_1, \dots, g_k$ in this order and whose representative x-fast trie is
obtained from the empty x-fast trie by inserting the last element of each nonempty group,
in order. No condition on the groups is checked here; when a group is sorted, its last
element is its maximum.
