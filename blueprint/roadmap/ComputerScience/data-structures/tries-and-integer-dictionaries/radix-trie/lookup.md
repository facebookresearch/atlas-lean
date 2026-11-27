# Radix trie lookup

Looking up a key, a list over $\alpha$, in a radix trie returns an
optional value. At a node, the empty key returns the value stored at the node, if any. A
nonempty key $k$ with first symbol $c$ goes to the first child edge whose label starts with $c$.
If there is no such edge, or its label $\ell$ is not a prefix of $k$, the lookup returns no
value; otherwise it continues in the subtree of that edge with $k$ minus its first $|\ell|$
symbols.
