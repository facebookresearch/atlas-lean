# Lookup in a radix trie built from a list with distinct keys

Let $L$ be a list of
key-value pairs, whose keys are lists over $\gamma$, in which no key occurs twice. If the pair
$(k, v)$ occurs in $L$, then looking up $k$ in the radix trie built from $L$ returns $v$.
