# Batcher's odd-even merger

For $k \in \mathbb{N}$, the odd-even merger on wires
$0, \dots, 2^{k+1} - 1$ is the comparator list defined by recursion on $k$. For $k = 0$ it is the
single comparator $(0, 1)$. For $k + 1$ it is the merger for $k$ with each wire $i$ renamed to
$2i$ (merging the even wires), followed by the merger for $k$ with each wire $i$ renamed to
$2i + 1$ (merging the odd wires), followed by the comparators $(2i + 1, 2i + 2)$ for
$i = 0, 1, \dots, 2^{k+1} - 2$ in increasing order of $i$.
