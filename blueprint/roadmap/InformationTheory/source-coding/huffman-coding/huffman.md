# Huffman's algorithm

Let $L$ be a list of $n$ pairs $(a_0, w_0), \dots, (a_{n-1}, w_{n-1})$
of symbols and natural-number weights, with decidable equality on symbols. The construction
fails when $L$ is empty or two pairs share a symbol. Otherwise it starts from $n$ leaves, the
leaf for $(a_i, w_i)$ having priority (weight $w_i$, serial $i$), and performs $n - 1$ merges:
each merge removes the two trees whose priorities are least in the lexicographic order on
(weight, serial), and adds the fork with the first removed tree on the left, with priority the
sum of the two weights and the next unused serial $n, n + 1, \dots$. If exactly one tree then
remains, it is returned; otherwise the construction fails.

Ties between equal weights are broken by serial: leaves come before merged trees, leaves in input
order and merged trees in creation order.
