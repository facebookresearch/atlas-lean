# Entries of a radix trie

The entries of a radix trie are its key-value pairs, listed
recursively. For a node with child edges $(\ell_1, t_1), \dots, (\ell_n, t_n)$ in stored order,
the list starts with the pair $(\varepsilon, v)$, where $\varepsilon$ is the empty key, if the
node stores a value $v$; it continues with the entries of $t_1$ with $\ell_1$ prepended to
every key, then the entries of $t_2$ with $\ell_2$ prepended, and so on up to $t_n$.
