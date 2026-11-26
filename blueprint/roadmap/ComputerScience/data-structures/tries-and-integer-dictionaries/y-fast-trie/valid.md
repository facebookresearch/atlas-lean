# Validity of a grouped y-fast trie

A grouped y-fast trie $t$ over keys in
$\{0, \dots, 2^w - 1\}$ with group bound $B$ is valid when its representative trie is a valid
x-fast trie; a key $r$ is stored in the representative trie exactly when $r$ is the last element
of some group of $t$; every group of $t$ is nonempty, has at most $B$ keys, and is strictly
increasing; and the groups of $t$ are ordered, that is, every key of an earlier group is smaller
than every key of a later group.
