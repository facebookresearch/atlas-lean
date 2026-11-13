# Radix trie

For types $\alpha$ and $\beta$, a radix trie with keys that are lists over
$\alpha$ and values in $\beta$ is a node made of an optional value in $\beta$ and a finite list of
child edges, each a pair of a label, which is a list over $\alpha$, and a radix trie (the
subtree at the end of the edge).

No invariant is built into the type: labels may be empty and sibling labels may share first
symbols. The radix-trie invariant is imposed separately.
