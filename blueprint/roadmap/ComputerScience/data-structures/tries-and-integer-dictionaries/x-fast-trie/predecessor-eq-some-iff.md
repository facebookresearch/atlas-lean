# Characterization of the x-fast trie predecessor

For an x-fast trie $t$ over
$w$-bit keys and keys $x, y < 2^w$, the predecessor query of $x$ in $t$ returns $y$ if and
only if $y$ is stored in $t$, $y < x$, and every key $z$ stored in $t$ with $z < x$
satisfies $z \le y$.
