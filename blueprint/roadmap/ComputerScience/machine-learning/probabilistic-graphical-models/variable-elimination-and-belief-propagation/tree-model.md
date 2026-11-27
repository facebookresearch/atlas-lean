# Pairwise model on a tree

For a type $\alpha$ of values and $n \in \mathbb{N}$, a pairwise
tree model on the vertices $0, \dots, n$ consists of a parent $p(k + 1) \in \{0, \dots, k\}$ for
each vertex $k + 1$ with $k < n$ (so vertex $0$ is the root and every vertex comes after its
parent), a unary factor $\varphi_i : \alpha \to \mathbb{R}$ for each vertex $i \le n$, and for each
$k < n$ a pairwise factor $\psi_k(a, b) \in \mathbb{R}$ on the edge between vertex $k + 1$ and its
parent, defined for all $a, b \in \alpha$, where $a$ is the value at vertex $k + 1$ and $b$ the
value at its parent.
