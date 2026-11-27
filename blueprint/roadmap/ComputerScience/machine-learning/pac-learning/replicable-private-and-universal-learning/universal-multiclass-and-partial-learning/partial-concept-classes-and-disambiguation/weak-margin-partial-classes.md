# Partial classes from weak-margin realizability have bounded VC dimension and finite disambiguations

Let $B \subseteq \{0,1\}^X$ be a base class of VC dimension $d$ and $\gamma \in (0,1]$. Call a sample $\gamma$-realizable with respect to $B$ if for every distribution $D$ over the sample some $b \in B$ has $\Pr_{(x,y) \sim D}[b(x) \ne y] \le (1-\gamma)/2$, and let $H_\gamma$ be the partial class whose realizable samples are exactly the $\gamma$-realizable ones (the class of concepts learnable by boosting weak learners from $B$ with edge $\gamma$). Then $\mathrm{VC}(H_\gamma) = O\big(\frac{d}{\gamma^2}\log\frac{d}{\gamma}\big) = \tilde O(d/\gamma^2)$, so $H_\gamma$ is PAC learnable with sample complexity $\tilde O(d/(\gamma^2\varepsilon))$, and $H_\gamma$ admits a disambiguation by a total class of comparable VC dimension (weighted majority votes of $O(\log(m)/\gamma^2)$ base hypotheses on samples of size $m$).

## Proof sketch

By the minimax theorem, a $\gamma$-realizable sample is labelled correctly by a weighted majority of base hypotheses with margin $\gamma$, and by sampling, by an unweighted majority of $T = O(\log m/\gamma^2)$ of them. The class of such majorities has VC dimension $O(Td\log T)$, and a shattered set of size $m$ must satisfy $m \le O(Td\log T)$ with $T$ depending on $m$ logarithmically, which solves to the stated bound. The majority-vote class is itself the disambiguation.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)
- [The weighted majority vote](../../../../online-learning-and-boosting/boosting-and-the-minimax-theorem/weighted-vote.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [Von Neumann's minimax theorem](../../../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
