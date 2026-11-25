# Boolean function computed by a decision tree

The output of a [decision tree](decision-tree.md) $T$ on a set $E$ at $\omega \in \{0, 1\}^E$ is defined recursively: a leaf labelled $b$ outputs $b$, and a node labelled $e$ with subtrees $t$ and $f$ outputs the output of $t$ at $\omega$ if $\omega_e = 1$ and that of $f$ if $\omega_e = 0$.
