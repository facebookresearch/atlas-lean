# Variables queried by a decision tree on an input

For a [decision tree](decision-tree.md) $T$ on a set $E$ and $\omega \in \{0, 1\}^E$, the set of variables queried by $T$ on input $\omega$ is defined recursively: it is empty for a leaf, and for a node labelled $e$ with subtrees $t$ and $f$ it is $\{e\}$ together with the set queried by $t$ on $\omega$ if $\omega_e = 1$, and by $f$ if $\omega_e = 0$.
