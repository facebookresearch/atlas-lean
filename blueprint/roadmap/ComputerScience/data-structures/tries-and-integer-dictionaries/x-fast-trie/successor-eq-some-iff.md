# Characterization of the x-fast trie successor

Let $t$ be an x-fast trie over $w$-bit
keys and let $x$ and $y$ be keys in $\{0, \dots, 2^w - 1\}$. The successor of $x$ in $t$ exists
and equals $y$ if and only if $y$ is a stored key of $t$, $x < y$, and $y \le z$ for every stored
key $z$ of $t$ with $x < z$.
