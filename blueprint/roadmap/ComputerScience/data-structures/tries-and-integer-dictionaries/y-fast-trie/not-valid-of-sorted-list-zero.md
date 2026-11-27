# Building from a nonempty list with group bound zero gives an invalid trie

For every
natural number $w$ and every nonempty list $l$ of $w$-bit keys, the grouped y-fast trie with
group bound $B = 0$ built from $l$ is not valid.

With $B = 0$ the only group is $l$ itself, which has more than $0$ keys. For $B > 0$ and strictly
increasing $l$, the grouped y-fast trie built from $l$ is valid.
