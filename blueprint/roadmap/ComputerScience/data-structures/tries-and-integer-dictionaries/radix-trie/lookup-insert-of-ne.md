# Insertion into a radix trie leaves lookups of other keys unchanged

For every radix
trie $T$, all keys $k \ne k'$ and every value $v$, looking up $k$ in the trie obtained from $T$
by inserting $v$ at $k'$ gives the same result as looking up $k$ in $T$.
