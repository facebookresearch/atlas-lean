# Complement of a Boolean quadtree

The complement of a Boolean region quadtree is defined recursively: the complement of a leaf
$L(b)$ is $L(\lnot b)$, and the complement of a branch $Q(t_0, t_1, t_2, t_3)$ is the compressing
branch constructor applied to the complements of $t_0, t_1, t_2, t_3$.
