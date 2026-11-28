# Partial classes from weak-margin realizability have bounded VC dimension and finite disambiguations

Let $B \subseteq \{0,1\}^X$ be a base class of VC dimension $d$ and $\gamma \in (0,1]$. Call a sample $\gamma$-realizable with respect to $B$ if for every distribution $D$ over the sample some $b \in B$ has $\Pr_{(x,y) \sim D}[b(x) \ne y] \le (1-\gamma)/2$, and let $H_\gamma$ be the partial class whose realizable samples are exactly the $\gamma$-realizable ones (the class of concepts learnable by boosting weak learners from $B$ with edge $\gamma$). Then $\mathrm{VC}(H_\gamma) = O\big(\frac{d}{\gamma^2}\log\frac{d}{\gamma}\big) = \tilde O(d/\gamma^2)$, and $H_\gamma$ admits a disambiguation by a total class $\bar H_\gamma$ with $\mathrm{VC}(\bar H_\gamma) = \tilde O(d\, d^*/\gamma^2)$, where $d^* \le 2^{d+1}$ is the dual VC dimension of $B$: the class of majority votes of $k = O(d^*/\gamma^2)$ hypotheses from $B$.

## Proof sketch

By the minimax theorem, a $\gamma$-realizable sample is labelled correctly by a distribution over base hypotheses with margin $\gamma$. Sampling $T = O(\log m/\gamma^2)$ hypotheses from it gives a majority vote correct on the whole sample, so a shattered set of size $m$ is shattered by majorities of $T$ base hypotheses, whose class has VC dimension $O(Td \log T)$; solving $m \le O(Td\log T)$ gives the VC bound. For the disambiguation, uniform convergence over the dual class (an $\varepsilon$-approximation of size depending on $d^*$ rather than on $m$) replaces sampling, so majorities of $k = O(d^*/\gamma^2)$ base hypotheses realize every $\gamma$-realizable sample, and the VC bound for such majorities gives $\tilde O(d\, d^*/\gamma^2)$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)
- [The weighted majority vote](../../../../online-learning-and-boosting/boosting-and-the-minimax-theorem/weighted-vote.md)
- [Assouad's dual VC dimension bound](../../../sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/assouad-dual-vc-dimension-bound.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Section 3.2, Definition 18, Theorem 19 (after Alon, Gonen, Hazan and Moran, 2020) and Theorem 20.
