# Node constructor restoring the leftist property

Given an element $x$ and two leftist heaps $a$ and $b$, the node built from $x$, $a$ and $b$ is
$\langle \operatorname{rank}(b) + 1, x, a, b \rangle$ if $\operatorname{rank}(a) \ge
\operatorname{rank}(b)$, and $\langle \operatorname{rank}(a) + 1, x, b, a \rangle$ otherwise. Thus
the subheap of larger rank becomes the left child, and the stored rank is one plus the rank of the
right child.
