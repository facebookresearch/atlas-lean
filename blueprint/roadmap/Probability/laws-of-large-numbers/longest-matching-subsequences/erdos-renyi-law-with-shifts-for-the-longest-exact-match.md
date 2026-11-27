# Erdős–Rényi law with shifts for the longest exact match

Let $X_1, X_2, \dots$ and $Y_1, Y_2, \dots$ be independent sequences with the same distribution, and let $M_n = \max\{m : X_{i+k} = Y_{j+k} \text{ for } k = 1, \dots, m, \text{ for some } 0 \le i, j \le n - m\}$ be the length of the longest common contiguous match between $X_1 \cdots X_n$ and $Y_1 \cdots Y_n$, allowing shifts. Arratia and Waterman (1985, Theorem 2) prove that if the letters are i.i.d. with $0 < p = P(X_1 = Y_1) < 1$ (so $p = \sum_a q_a^2$ for letter distribution $q$), then for every $\varepsilon > 0$, almost surely

$$\frac{M_n - 2\log_{1/p} n}{\log_{1/p}\log_{1/p} n} \in (-4 - \varepsilon,\ 1 + \varepsilon) \quad \text{eventually};$$

in particular $P(\lim_n M_n/\log_{1/p} n = 2) = 1$, twice the Erdős–Rényi growth of the longest head run without shifts. Theorem 3 gives the analogous result for independent irreducible aperiodic Markov chains on a finite alphabet, with $p$ the largest eigenvalue of the matrix of squared transition probabilities. Corollary 1, deduced from the result for deletions only (Theorem 4), shows that the longest match allowing shifts and at most $k$ deletions, insertions, substitutions or transpositions, divided by $\log_{1/p} n$, still tends to $2$ in probability when $k = o(\log n/\log\log n)$; Section 4 treats sequences of unequal lengths.

## Depends on

- [Finite-state Markov chain with a given transition matrix](../../../Probability/markov-chains/finite-markov-chains/is-finite-markov-chain.md)

## Expansion

1. The model, the definition of $M_n$, and the heuristic that $n^2$ starting pairs balance the probability $p^m$ of a match of length $m$.
2. The upper bound $P(M_n - 2\log_{1/p} n > b) \le cp^b$ by a first-moment count of matching pairs of windows, inequality (4), and its almost-sure form along a subsequence.
3. The lower bound by a second-moment estimate for the number of matches, with the dependence of overlapping windows controlled as in the proof of Theorem 1 (uniform letters) and Theorem 2.
4. The second-order bounds of Theorem 2.
5. The Markov case (Theorem 3), matches with deletions (Theorem 4, Corollary 1) and unequal lengths (Section 4), as separate statements.

## Sources

- R. Arratia and M. S. Waterman, An Erdős–Rényi law with shifts, Adv. Math. 55 (1985), 13–23, Theorems 1–4 and Corollary 1. <https://doi.org/10.1016/0001-8708(85)90003-9>
