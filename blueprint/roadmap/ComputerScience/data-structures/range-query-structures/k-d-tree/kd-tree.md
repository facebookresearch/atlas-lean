# Kd-trees

A kd-tree over points of $\mathbb{Z}^d$ is either empty, a leaf holding one
point of $\mathbb{Z}^d$, or a split node holding a split axis $a \in \{0, \dots, d-1\}$, a split
value $s \in \mathbb{Z}$ and two kd-trees, its left and right subtrees.
