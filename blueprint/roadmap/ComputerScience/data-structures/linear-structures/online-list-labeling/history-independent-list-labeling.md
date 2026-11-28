# History-independent list labeling

A randomized list-labeling algorithm is *history independent* if its whole current state, the array together with any metadata the algorithm keeps, reveals nothing about past operations beyond the current set $S$ of stored elements: for every $S$, the distribution of the state depends only on $S$ and not on the sequence of insertions and deletions that produced $S$. The whole state stores the elements themselves, so it always reveals $S$ (an array holding one key reveals whether that key is $a$ or $b$), and whole-state history independence is conditional on $S$. The source's remark that an adversary can deduce only the number of elements (Section 2) concerns the rank-only view: since a list-labeling algorithm sees the stored elements only through their relative order, the state with each element replaced by its rank among the stored elements has a distribution that depends only on $|S|$. In particular, whenever $n'$ elements are stored, the *array configuration* (the vector in $\{0,1\}^m$ marking the occupied slots) is distributed according to a fixed distribution $\mathcal{C}_{n',m}$ that depends only on $n'$ and $m$ (Property 1(a)). The converse fails: an algorithm with canonically distributed occupancy can still record its history in metadata. A deterministic algorithm is history independent only if each configuration is a fixed function of $n'$.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763, Section 2.
