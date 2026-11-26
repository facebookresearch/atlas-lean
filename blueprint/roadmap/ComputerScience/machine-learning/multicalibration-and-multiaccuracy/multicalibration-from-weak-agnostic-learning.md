# Multicalibration is efficiently reducible to weak agnostic learning of the group class

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Suppose $\mathcal{C}$ admits a weak agnostic learner: given samples from any distribution over $X \times [-1,1]$ for which some $c \in \mathcal{C}$ has correlation at least $\alpha$ with the label, it outputs $h$ (possibly outside $\mathcal{C}$, with bounded range) with correlation at least $\mathrm{poly}(\alpha)$. Then an $\alpha$-multicalibrated (with respect to $\mathcal{C}$) predictor can be computed with a number of weak-learner calls and samples polynomial in $1/\alpha$, by using the weak learner as the auditor on residuals $y - v$ restricted to level sets. Conversely, efficient auditing for multiaccuracy with respect to $\mathcal{C}$ yields efficient weak agnostic learning of $\mathcal{C}$, so the computational complexity of multicalibration is governed by agnostic learning of $\mathcal{C}$.

## Proof sketch

The residual $y - v$ on the level set $\{p = v\}$ is a labelled distribution on which a violating $c$ has correlation at least $\alpha$, so the weak learner returns a correction direction $h$ with correlation $\mathrm{poly}(\alpha)$, and the potential argument still applies with $h$ in place of $c$. For the converse, run the auditor on the constant predictor relative to relabelled data: a reported multiaccuracy violation is precisely a hypothesis correlated with the labels.

## Depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)
- [Learners and agnostic PAC learnability](../pac-learning/agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)
- [Learners and agnostic PAC learnability](../pac-learning/agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389.
