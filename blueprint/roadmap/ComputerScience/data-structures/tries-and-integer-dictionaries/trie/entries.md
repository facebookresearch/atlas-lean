# Entries of a trie

The entries of a trie are the list of its key-value pairs, where a key
is a list of letters. If the root stores a value $v$, the list begins with the pair consisting of
the empty key and $v$; it continues, for each child in the stored sibling order, with the entries
$(k, w)$ of that child, in order, each rewritten as $(a k, w)$, where $a$ is the letter labelling
the child and $a k$ is the key $k$ with $a$ prepended.
