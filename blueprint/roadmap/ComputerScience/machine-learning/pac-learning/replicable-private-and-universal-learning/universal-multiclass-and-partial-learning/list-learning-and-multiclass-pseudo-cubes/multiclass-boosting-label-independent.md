# Multiclass boosting with label-independent oracle complexity

There is an efficient boosting algorithm which, given oracle access to a $\gamma$-weak multiclass learner (in the list-relative sense) for a class $H \subseteq Y^X$, outputs a $(k-1)$-list predictor whose list error on every $H$-realizable distribution is at most $\varepsilon$ with probability $1-\delta$, using a number of weak-learner calls and samples bounded by a function of $\gamma$, $k$, $\varepsilon$ and $\delta$ only, with no dependence on $|Y|$. As consequences, multiclass weak learnability in this sense is equivalent to $(k-1)$-list PAC learnability (ordinary PAC learnability when $k = 2$), boosting extends to list learners, and the characterization of multiclass and list PAC learnability by the DS and $k$-DS dimensions admits a simplified proof through boosting.

## Proof sketch

The booster maintains multiplicative weights over the sample and in each round runs the weak learner; the weak hypotheses are aggregated not by a weighted vote over $Y$ but into a short list of labels per point, since beating $1/k$ certifies that the correct label is among a few heavily voted labels. A second stage learns within the induced menu, where the effective label set has bounded size, by ordinary boosting. The analysis is a potential argument on the weights in which $|Y|$ never enters.

## Depends on

- [Multiclass weak learnability relative to random guessing on lists](multiclass-weak-learning-condition.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Weak learnability implies PAC learnability via boosting](../../../../generalization-bounds-and-concentration/weak-learnability-implies-pac-learnability-via-boosting.md)
- [The k-DS dimension characterizes k-list learnability](k-ds-dimension-characterizes-list-learnability.md)

## Sources

- N. Brukhim, A. Daniely, Y. Mansour, S. Moran, "Multiclass Boosting: Simple and Intuitive Weak Learning Criteria", NeurIPS (2023), arXiv:2307.00642.
