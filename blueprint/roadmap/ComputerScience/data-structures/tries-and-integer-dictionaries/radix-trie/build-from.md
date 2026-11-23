# Radix trie built from a list of key-value pairs

The trie built from the empty list is the
empty trie, and the trie built from a list with head $(k, v)$ and tail $L$ is the trie built from
$L$ with the value $v$ inserted at the key $k$. Later pairs in the list are thus inserted first,
so on duplicate keys the head-most value wins.
