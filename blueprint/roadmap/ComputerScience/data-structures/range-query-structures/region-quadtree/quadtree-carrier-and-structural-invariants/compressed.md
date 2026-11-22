# Compressed quadtree

Compression of a region quadtree is defined recursively: every leaf is compressed, and a branch
$Q(t_0, t_1, t_2, t_3)$ is compressed exactly when its four children are compressed and it is not
the case that $t_0 = t_1 = t_2 = t_3 = L(a)$ for some value $a$. Four equal children that are
branches are allowed.
