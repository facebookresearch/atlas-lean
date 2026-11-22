# Suffix tree

For a list $s = (s_0, \dots, s_{n-1})$ over $\alpha$, let
$\hat s = (\mathrm{some}\,s_0, \dots, \mathrm{some}\,s_{n-1}, \mathrm{none})$ be its
terminated string over $\mathrm{Option}\,\alpha$. The suffix tree of $s$ is the radix trie
with keys over $\mathrm{Option}\,\alpha$ and natural-number values obtained from the empty
trie by inserting, for $i = n, n - 1, \dots, 0$ in this order, the suffix of $\hat s$
starting at index $i$ with value $i$.
