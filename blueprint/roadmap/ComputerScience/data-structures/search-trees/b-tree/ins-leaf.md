# Insertion into a B-tree leaf

Over a linearly ordered key type, let $t$ be a natural
number, $x$ a key, $K$ the key list of a leaf, and $K'$ the result of ordered insertion of $x$
into $K$. If $K'$ has at most $2t - 1$ keys, the insertion result is the single leaf with keys
$K'$. Otherwise the leaf is split: the result consists of the leaf holding the first $t - 1$ keys
of $K'$, the next key of $K'$ promoted as the median, and the leaf holding the remaining keys.
Here subtraction of natural numbers is truncated at $0$.
