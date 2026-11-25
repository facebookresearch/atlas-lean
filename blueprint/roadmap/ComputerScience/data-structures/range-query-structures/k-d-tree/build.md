# Kd-tree construction by median splits

Let $d \ge 1$, let $a \in \{0, \dots, d-1\}$ be
an axis and let $P$ be a list of points in $\mathbb{Z}^d$. The kd-tree built from $P$ starting at
axis $a$ is the empty tree if $P$ is empty and the leaf holding $p$ if $P = [p]$. If $P$ has
$n \ge 2$ points, sort $P$ by $a$-coordinate with merge sort, let $L$ be the first
$\lfloor n/2 \rfloor$ points of the sorted list and $R$ the remaining ones. The result is the
split node with axis $a$ whose split value is the $a$-coordinate of the first point of $R$, whose
left subtree is built from $L$ and whose right subtree is built from $R$, both starting at the
next axis $(a + 1) \bmod d$.
