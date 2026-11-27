# The map $V_{TBZ}$ from SZ indices to TBZ words

For an index $k = (k_1, \dots, k_r)$ of
natural numbers, $V_{TBZ}(k)$ is the formal $\mathbb{Q}$-linear combination of TBZ words (words in
the letters $\bar 1$ and $j \ge 1$; write $z_a$ for the one-letter word $a$) obtained by replacing
each letter $k_i = 0$ by $z_1 - z_{\bar 1}$ and each letter $k_i \ge 1$ by
$\sum_{j=1}^{k_i} (-1)^{k_i - j} z_{j'}$, where $j' = \bar 1$ for $j = 1$ and $j' = j$ otherwise,
and multiplying out by concatenation of words. The empty index goes to the empty word with
coefficient $1$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 9 (ii) (the map `V_TBZ`).
