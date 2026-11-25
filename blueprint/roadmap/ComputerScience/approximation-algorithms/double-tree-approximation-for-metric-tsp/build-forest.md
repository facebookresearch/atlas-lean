# Forest of a parent array below a vertex

Let $p$ assign to each vertex of
$\{0, \dots, n-1\}$ either a parent or nothing. For $k \in \mathbb{N}$ and a vertex $v$, the
forest below $v$ of depth $k$ is empty when $k = 0$. For depth $k + 1$ it has one tree for each
child $c$ of $v$ (each vertex whose parent is $v$), in increasing order of $c$, namely $c$ with
the forest below $c$ of depth $k$ as its subtrees.
