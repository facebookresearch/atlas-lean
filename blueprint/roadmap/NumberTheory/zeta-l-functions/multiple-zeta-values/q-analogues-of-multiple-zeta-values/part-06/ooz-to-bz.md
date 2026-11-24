# The map $U$ from OOZ to BZ words

A word is a finite sequence $z_{k_1} \cdots z_{k_r}$ of
letters $z_k$, $k \in \mathbb{N}$. The map $U$ sends each word to a formal $\mathbb{Q}$-linear
combination of words: $U(\mathbf{1}) = \mathbf{1}$ for the empty word $\mathbf{1}$, and for
$r \ge 1$

$$U(z_{k_1} \cdots z_{k_r}) = \sum \binom{k_1 - 2}{n_1 - 2} \binom{k_2 - 1}{n_2 - 1} \cdots
\binom{k_r - 1}{n_r - 1} \, z_{n_1} \cdots z_{n_r}$$

where the sum runs over $2 \le n_1 \le k_1$ and $1 \le n_j \le k_j$ for $2 \le j \le r$ (an empty
sum is $0$).

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 12 (i) (after Ebrahimi-Fard, Manchon and Singer, the map `U`).
