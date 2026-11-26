# Linear-probing probe sequence

Given a hash function $h : K \to \mathbb{N}$ and a
number of slots $m > 0$, the $i$-th probe of a key $k$ is the slot $(h(k) + i) \bmod m$ in
$\{0, \dots, m - 1\}$.
