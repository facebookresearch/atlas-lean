# Double-hashing probe sequence

Given hash functions $h_1, h_2 : K \to \mathbb{N}$ and a
number of slots $m > 0$, the $i$-th probe of a key $k$ is the slot
$(h_1(k) + i \cdot h_2(k)) \bmod m$ in $\{0, \dots, m - 1\}$.
