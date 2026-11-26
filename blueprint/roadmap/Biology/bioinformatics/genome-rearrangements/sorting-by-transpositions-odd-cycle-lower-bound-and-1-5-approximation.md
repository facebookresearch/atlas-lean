# Sorting by transpositions: odd-cycle lower bound and a 1.5-approximation

For a permutation $\pi$ of $\{1, \dots, n\}$ framed by $0$ and $n + 1$, a transposition moves a contiguous block to another position. Let $d(\pi)$ be the transposition distance. The cycle graph $G(\pi)$ has vertices $0, 1, \dots, n + 1$, a gray edge from $i - 1$ to $i$ and a black edge from $\pi_i$ to $\pi_{i-1}$ for each $1 \le i \le n + 1$ (with $\pi_0 = 0$, $\pi_{n+1} = n + 1$); it decomposes uniquely into alternating cycles. Every alternating cycle has even total length, so length is counted in black edges: a $k$-cycle has $k$ black edges (and $2k$ edges), it is odd if $k$ is odd, and long if $k > 2$. Let $c(\pi)$ be the total number of cycles and $c_{\mathrm{odd}}(\pi)$ the number of odd cycles. A transposition changes $c$ by $-2$, $0$ or $2$ (Lemma 2.1, giving $d(\pi) \ge (n + 1 - c(\pi))/2$, Theorem 2.2) and changes $c_{\mathrm{odd}}$ by $-2$, $0$ or $2$ (Lemma 2.3), and the identity has $n + 1$ cycles, all odd $1$-cycles; hence Bafna and Pevzner (1998, Theorem 2.4) obtain $d(\pi) \ge (n + 1 - c_{\mathrm{odd}}(\pi))/2$, which gives $d(n\ n{-}1 \cdots 1) \ge \lfloor n/2 \rfloor$ for the reversed permutation. Their algorithm TransSort, running in $O(n^2)$ time, performs a valid $2$-move or a valid $0$-move followed by two valid $2$-moves while a long cycle exists (Theorem 6.8), and a good $0$-move followed by a valid $2$-move when only short cycles remain (Theorem 6.9). It sorts $\pi$ with at most $\frac34(n + 1 - c_{\mathrm{odd}}(\pi))$ transpositions, a performance guarantee of $1.5$ (Corollary 6.10); consequently the transposition diameter of $S_n$ is at most $3n/4$ (Corollary 6.11).

## Expansion

1. Definitions: transpositions, the cycle graph and its unique alternating cycle decomposition, cycle length counted in black edges, odd and even cycles, long and short cycles, and the total cycle count $c(\pi)$ versus $c_{\mathrm{odd}}(\pi)$.
2. Theorem 2.2 from the change of $c$ (Lemma 2.1), and Theorem 2.4: the change of $c_{\mathrm{odd}}$ under one transposition (Lemma 2.3) and the lower bound.
3. Oriented and nonoriented cycles, valid and good moves, and Theorems 6.8–6.9 by case analysis (Lemmas 6.1–6.7).
4. Corollary 6.10: the algorithm, its $O(n^2)$ running time and its guarantee; Corollary 6.11: the diameter bound.
5. Later questions: the [approximation ratio for sorting by transpositions](../../../Biology/bioinformatics/approximation-ratio-for-sorting-by-transpositions.md) and the [transposition diameter of the symmetric group](../../../Biology/bioinformatics/transposition-diameter-of-the-symmetric-group.md).

## Sources

- V. Bafna and P. A. Pevzner, Sorting by transpositions, SIAM J. Discrete Math. 11 (1998), 224–240, Section 2, Theorems 2.2 and 2.4, Theorems 6.8–6.9 and Corollaries 6.10–6.11. <https://doi.org/10.1137/S089548019528280X>
