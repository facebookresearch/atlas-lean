# Successor in the trie built from a sorted list

Let $B > 0$, let $l$ be a strictly
increasing list of $w$-bit keys, and let $x$, $y$ be keys. The successor query for $x$ in the
grouped y-fast trie built from $l$ with group bound $B$ returns $y$ if and only if $y$ belongs
to $l$, $x < y$, and $y \le z$ for every $z$ in $l$ with $x < z$.
