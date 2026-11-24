# Long weighted zero-sum free sequences in finite products of cyclic groups

Let $r$ and
$\beta$ be natural numbers and let $n_1, \dots, n_r$ be natural numbers. Then there is a
sequence $s$ over $\mathbb{Z}/n_1\mathbb{Z} \oplus \dots \oplus \mathbb{Z}/n_r\mathbb{Z}$ of
length $\sum_{i=1}^{r} (\lceil n_i/\beta \rceil - 1)$ that is $\{1, \dots, \beta\}$-weighted
zero-sum free: for every non-empty set $I$ of positions and all weights
$a_i \in \{1, \dots, \beta\}$, the weighted sum $\sum_{i \in I} a_i s_i$ is non-zero. Here
$\lceil n_i/\beta \rceil - 1$ is computed in $\mathbb{N}$, so it is $0$ when $n_i = 0$ or
$\beta = 0$.

The sequence consists of $\lceil n_i/\beta \rceil - 1$ copies of the $i$-th coordinate generator
for each $i$. In a coordinate $i$ whose block meets $I$, the selected weights add up to a number
between $1$ and $(\lceil n_i/\beta \rceil - 1)\beta < n_i$, so that coordinate of the weighted sum
is non-zero.
