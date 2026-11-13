# An inserted key passes the membership test

For every x-fast trie $t$ over $w$-bit keys
and every $w$-bit key $x$, the membership test at $x$ of the trie obtained by inserting $x$ into
$t$ returns true.

No validity assumption on $t$ is needed: insertion puts the full-length prefix of $x$ directly
into the deepest level, which is the level the membership test probes.
