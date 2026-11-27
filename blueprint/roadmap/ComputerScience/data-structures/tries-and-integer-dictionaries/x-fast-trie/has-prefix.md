# Level probe of an x-fast trie

For an x-fast trie $t$ over $w$-bit keys, a level
$0 \le l \le w$ and a $w$-bit key $x$, the probe of level $l$ of $t$ at $x$ returns true exactly
when the $l$-bit prefix of $x$ belongs to the prefix set stored at level $l$ of $t$.

When $t$ is valid, this holds exactly when some key stored in $t$ has the same $l$-bit prefix
as $x$.
