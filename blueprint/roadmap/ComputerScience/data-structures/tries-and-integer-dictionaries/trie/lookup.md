# Trie lookup

The lookup of a key (a list over $\alpha$) in a trie returns an optional
value in $\beta$, by recursion on the key. For the empty key it is the optional value stored at
the root. For a key with first letter $a$ followed by the key $k$, it fails if no child of the
root is labelled $a$, and otherwise it is the lookup of $k$ in the first child labelled $a$.
