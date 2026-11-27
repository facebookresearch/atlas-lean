# Cost-sensitive boosting dichotomy for binary classification

Let $Y = \{-1,+1\}$ and let $w = (w_+, w_-) \in (0,1]^2$ be the costs of a false negative and a false positive, so that the cost-sensitive loss of $h$ under $D$ is $L^w_D(h) = w_+ \Pr[h(x) = -1, y = +1] + w_- \Pr[h(x) = +1, y = -1]$. Call a learner a $(w,z)$-learner for a class $F$ if on every $F$-realizable $D$ it outputs, from enough samples, hypotheses with $L^w_D(h) \le z + \varepsilon$ for every $\varepsilon > 0$. Then for every $z \ge 0$ exactly one of the following holds:

- every $(w,z)$-learner, for every class $F \subseteq Y^X$, can be boosted to a $(w,0)$-learner;
- there is a single random guess (a data-independent randomized constant hypothesis) that is a $(w,z)$-learner for every class.

The threshold is the value of the zero-sum game defined by $w$: the first case holds if and only if $z < V(w) = \dfrac{w_+ w_-}{w_+ + w_-}$. For $w = (1,1)$, up to normalization, this recovers the classical threshold one half for weak learning.

## Proof sketch

A random guess predicting $+1$ with probability $q$ has loss at most $\max(w_+ (1-q), w_- q)$ under any label distribution, minimized at $q = w_+/(w_+ + w_-)$ with value $V(w)$, which shows guarantees $z \ge V(w)$ are trivial. For $z < V(w)$, von Neumann's minimax theorem applied to the cost-weighted game turns the weak learner into a distribution over hypotheses whose cost-weighted margin is positive on every example, and a reweighting booster in the style of AdaBoost then drives the cost-sensitive loss to zero. A third application of the minimax theorem shows that no intermediate guarantee exists.

## Depends on

- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [Weak learnability implies PAC learnability via boosting](../../../../generalization-bounds-and-concentration/weak-learnability-implies-pac-learnability-via-boosting.md)
- [The weak-learning assumption](../../../../online-learning-and-boosting/adaboost/weak-learner.md)

## Sources

- M. Bressan, N. Brukhim, N. Cesa-Bianchi, E. Esposito, Y. Mansour, S. Moran, M. Thiessen, "Of Dice and Games: A Theory of Generalized Boosting", COLT (2025), arXiv:2412.08012, Definitions 1 and 2 and Theorem A.
