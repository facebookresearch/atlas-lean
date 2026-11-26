# History-independent list labeling

A randomized list-labeling algorithm is *history independent* if, for every set $S$ of stored elements, the distribution of the array state depends only on $S$ and not on the sequence of insertions and deletions that produced $S$. History independence rules out deterministic algorithms and implies that an adversary learns nothing about past operations from the memory layout.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
