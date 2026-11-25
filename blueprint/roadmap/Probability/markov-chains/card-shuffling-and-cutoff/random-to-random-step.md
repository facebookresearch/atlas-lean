# Step law of the random-to-random shuffle

Let $n \in \mathbb{N}$ and label positions $0, 1, \dots, n-1$. For a position $i$ let $c_i$ be the cyclic permutation of positions with $c_i(k) = k + 1$ for $k < i$, $c_i(i) = 0$ and $c_i(k) = k$ for $k > i$. The step law of the random-to-random shuffle of $n$ cards is the probability function on permutations $\sigma$ of $\{0, \dots, n-1\}$

$$\mu_n(\sigma) = \frac{\#\{(i, j) : c_i^{-1} c_j = \sigma\}}{n^2},$$

the law of $c_i^{-1} c_j$ for independent uniform positions $i$ and $j$. A deck $d$, with $d(p)$ the card at position $p$, moves to $d \circ c_i^{-1} c_j$: the card at position $i$ is removed and reinserted at position $j$.
