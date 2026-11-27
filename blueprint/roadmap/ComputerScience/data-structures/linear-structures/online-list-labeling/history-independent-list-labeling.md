# History-independent list labeling

A randomized list-labeling algorithm is *history independent* if, for every set $S$ of stored elements, the distribution of the array state depends only on $S$ and not on the sequence of insertions and deletions that produced $S$. Since a list-labeling algorithm sees the stored elements only through their relative order, this says that whenever $n'$ elements are stored, the *array configuration* (the vector in $\{0,1\}^m$ marking the occupied slots) is distributed according to a fixed distribution $\mathcal{C}_{n',m}$ that depends only on $n'$ and $m$. An adversary who inspects the array therefore learns nothing about past operations beyond the current number of elements. A deterministic algorithm is history independent only if each configuration is a fixed function of $n'$.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
