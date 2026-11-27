# Cuckoo graph of a key set

Let $h_1, h_2 : X \to [r]$ and let $S \subseteq X$. The *cuckoo graph* of $S$ is the bipartite multigraph with vertex set $\{1\} \times [r] \cup \{2\} \times [r]$ (the slots of two sub-tables) and one edge $\{(1, h_1(x)), (2, h_2(x))\}$ for each key $x \in S$. A placement of $S$ storing each key in one of its two slots, with distinct keys in distinct slots, exists iff every connected component of the cuckoo graph has at most as many edges as vertices, i.e. contains at most one cycle.

## Depends on

- [Cuckoo hash table](../../cuckoo-hashing/cuckoo-hashing.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004.
