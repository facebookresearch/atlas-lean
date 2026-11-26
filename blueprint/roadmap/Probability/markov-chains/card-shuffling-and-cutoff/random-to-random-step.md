# Step law of the random-to-random shuffle

Let $n \in \mathbb{N}$ and label positions $0, 1, \dots, n-1$. For a position $i$ let $c_i$ be the cyclic permutation of positions with $c_i(k) = k + 1$ for $k < i$, $c_i(i) = 0$ and $c_i(k) = k$ for $k > i$. The step function of the random-to-random shuffle of $n$ cards assigns to each permutation $\sigma$ of $\{0, \dots, n-1\}$ the number

$$\mu_n(\sigma) = \frac{\#\{(i, j) : c_i^{-1} c_j = \sigma\}}{n^2},$$

with division by zero read as $0$. For $n = 0$ there is a single permutation and no position, and $\mu_0 = 0$. For $n > 0$, $\mu_n$ is the law of $c_i^{-1} c_j$ for independent uniform positions $i$ and $j$: a deck $d$, with $d(p)$ the card at position $p$, moves to $d \circ c_i^{-1} c_j$, so the card at position $i$ is removed and reinserted at position $j$.
