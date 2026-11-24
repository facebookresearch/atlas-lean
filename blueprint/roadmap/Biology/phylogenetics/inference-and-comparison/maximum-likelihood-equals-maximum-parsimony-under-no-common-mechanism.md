# Maximum likelihood equals maximum parsimony under no common mechanism

In the symmetric $r$-state model $N_r$ on a phylogenetic tree $T$, each edge $e$ carries a probability $p(e)$ of change to each particular other state, with $0 \le p(e) \le 1/r$ and $(r-1)p(e) + q(e) = 1$, where $q(e)$ is the probability of no change; for $r = 4$ this is the Jukes–Cantor model. Under no common mechanism, the edge probabilities of different characters vary independently. For a character $\chi$, $\max P(\chi \mid T)$ is the likelihood maximized over all edge probabilities. Bryant, Fischer, Linz and Semple (2016, Theorem 6) restate Theorem 5 of Tuffley and Steel (1997): for a sequence $S = (\chi_1, \dots, \chi_k)$ of $r$-state characters on the leaf set,
$$\max P(S \mid T) = r^{-PS(S, T) - k},$$
where $PS(S, T)$ is the parsimony score of $S$ on $T$, the sum over characters of the minimum number of edges with different states at their ends over extensions to the interior vertices. Hence maximum likelihood under no common mechanism and maximum parsimony rank all trees in the same order and choose the same trees.

## Expansion

1. The $N_r$ model with its edge-probability range, and the no-common-mechanism assumption, as in Section 4 of Bryant, Fischer, Linz and Semple.
2. The single-character case $\max P(\chi \mid T) = r^{-PS(\chi, T) - 1}$: the upper bound for every choice of edge probabilities, and its attainment by setting $p(e) = 0$ on edges without a change in a most parsimonious extension and $p(e) = 1/r$ on the others.
3. The product over characters, whose edge probabilities are independent, giving the sequence formula and the common ranking of trees. The parsimony score itself can be computed by [Fitch's algorithm](../../../Biology/phylogenetics/small-parsimony-problem/fitch-score-eq.md), which the argument does not use.
4. Failure of the equivalence when the substitution probabilities are bounded above or a molecular clock is imposed, and the inclusion of maximum likelihood trees among maximum parsimony trees under a sufficiently small upper bound, as recorded by Fischer and Thatte (2010), as separate statements.

## Sources

- C. Bryant, M. Fischer, S. Linz and C. Semple, On the quirks of maximum parsimony and likelihood on phylogenetic networks, arXiv:1505.06898v4 (2016), Section 4, Theorem 6 and equation (3). <https://arxiv.org/abs/1505.06898>
- M. Fischer and B. Thatte, Revisiting an equivalence between maximum parsimony and maximum likelihood methods in phylogenetics, Bull. Math. Biol. 72 (2010), 208–220, abstract. <https://doi.org/10.1007/s11538-009-9446-2>
- Original result: C. Tuffley and M. Steel, Links between maximum likelihood and maximum parsimony under a simple model of site substitution, Bull. Math. Biol. 59 (1997), 581–607. <https://doi.org/10.1007/bf02459467> The formula follows Bryant, Fischer, Linz and Semple, Theorem 6.
