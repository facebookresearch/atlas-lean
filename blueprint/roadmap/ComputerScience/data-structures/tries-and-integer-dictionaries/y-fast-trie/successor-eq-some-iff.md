# Successor query returns the least larger stored key

Let $t$ be a valid grouped y-fast
trie and let $x$, $y$ be keys. The successor query for $x$ in $t$ returns $y$ if and only if
$y$ is stored in $t$, $x < y$, and $y \le z$ for every key $z$ stored in $t$ with $x < z$.
