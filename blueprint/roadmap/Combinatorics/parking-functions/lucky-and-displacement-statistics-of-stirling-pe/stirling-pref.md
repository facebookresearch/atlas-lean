# Zero-based preferences of a word

Let $w = w_1 \cdots w_{2n}$ be a word of natural
numbers, read as the preferences of $2n$ cars for spots numbered $0, \dots, 2n - 1$. Car
$i \in \{1, \dots, 2n\}$ prefers the spot $(w_i - 1) \bmod 2n$, where $w_i - 1$ is truncated at
$0$. When every $w_i$ lies in $\{1, \dots, 2n\}$, for example when $w$ is a Stirling permutation
of order $n$, this is the spot $w_i - 1$, which is spot $w_i$ in the one-based numbering.

## Sources

- L. Colmenarejo et al., *On the Lucky and Displacement Statistics of Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7, Section 1 (Stirling permutations read as parking functions of length `2n`).
