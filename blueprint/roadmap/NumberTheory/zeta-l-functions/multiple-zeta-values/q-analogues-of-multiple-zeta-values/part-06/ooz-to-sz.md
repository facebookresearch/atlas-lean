# The map $V$ from OOZ to SZ words

Identify an index $(k_1, \dots, k_r)$ of natural
numbers with the word $p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$. The map $V$ sends
each such word to a formal $\mathbb{Q}$-linear combination of words: $V(\mathbf{1}) = \mathbf{1}$
for the empty word $\mathbf{1}$, and for $r \ge 1$

$$V(p^{k_1} y \cdots p^{k_r} y) = \sum \binom{k_1 - 1}{n_1 - 1} \binom{k_2}{n_2} \cdots
\binom{k_r}{n_r} \, p^{n_1} y \cdots p^{n_r} y$$

where the sum runs over $1 \le n_1 \le k_1$ and $0 \le n_j \le k_j$ for $2 \le j \le r$ (an empty
sum is $0$).

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`).
