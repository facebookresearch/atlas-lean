# x-fast trie

An x-fast trie over $w$-bit keys consists of a finite set of stored keys in
$\{0, \dots, 2^w - 1\}$ together with, for each level $l \in \{0, \dots, w\}$, a finite set of
natural numbers, intended to hold the $l$-bit prefixes of the stored keys.

The classical per-level hash tables are modeled as finite sets, so no $O(\log w)$ successor bound
(or any other running-time bound) is claimed.
