# Lookups in a radix trie built from a list come from the list

For every list $L$ of
key-value pairs, if looking up a key $k$ in the radix trie built from $L$ returns a value $v$,
then the pair $(k, v)$ occurs in $L$.
