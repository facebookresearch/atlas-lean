# Multicalibration implies multiaccuracy and calibration on every group

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). If $p$ is $\alpha$-multicalibrated with respect to $\mathcal{C}$, then $p$ is $\alpha$-multiaccurate with respect to $\mathcal{C}$, and for every $S$ with $\mathbf{1}_S \in \mathcal{C}$ the restriction of $p$ to $S$ is calibrated up to $\alpha$: $\sum_v \big|\mathbb{E}[(y - v)\mathbf{1}[p(x) = v, x \in S]]\big| \le \alpha$. In particular a multicalibrated predictor satisfies approximate calibration within each group, so by the Kleinberg–Mullainathan–Raghavan trade-off it cannot in general also balance false positive and false negative rates across groups with different base rates.

## Proof sketch

Multiaccuracy follows from the triangle inequality: $|\mathbb{E}[c(x)(y - p(x))]| = |\sum_v \mathbb{E}[c(x)(y - v)\mathbf{1}[p(x) = v]]| \le \alpha$. Calibration within $S$ is the multicalibration condition for $c = \mathbf{1}_S$. The fairness consequence applies the trade-off theorem to the group-wise calibrated scores.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)
- [Group fairness criteria for scores and classifiers](../algorithmic-fairness/group-fairness-criteria-for-scores-and-classifiers.md)

## Proof depends on

- [Kleinberg–Mullainathan–Raghavan trade-off theorem](../algorithmic-fairness/kleinbergmullainathanraghavan-trade-off-theorem.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
