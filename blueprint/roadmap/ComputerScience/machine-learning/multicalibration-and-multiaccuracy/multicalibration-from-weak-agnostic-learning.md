# Multicalibration is efficiently reducible to weak agnostic learning of the group class

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Suppose $\mathcal{C}$ admits a weak agnostic learner: given samples from any distribution over $X \times [-1,1]$ for which some $c \in \mathcal{C}$ has correlation at least $\alpha$ with the label, it outputs $h$ (possibly outside $\mathcal{C}$, with bounded range) with correlation at least $\mathrm{poly}(\alpha)$. Then an $\alpha$-multicalibrated (with respect to $\mathcal{C}$) predictor can be computed with a number of weak-learner calls and samples polynomial in $1/\alpha$, by using the weak learner as the auditor on residuals $y - v$ restricted to level sets. In Hébert-Johnson, Kim, Reingold and Rothblum's formulation, with sets $S \in \mathcal{C}$ and relative errors on the level sets of the sets with $|S| \ge \gamma|X|$, a $(\rho,\tau)$-weak agnostic learner with $\rho \le \alpha^2\lambda\gamma/2$ and $\tau = \mathrm{poly}(\alpha,\lambda,\gamma)$ running in time $T$ gives an $(\alpha,\lambda)$-multicalibrated predictor in time $T \cdot \mathrm{poly}(1/\alpha, 1/\lambda, 1/\gamma)$, where $\lambda$ is the width of the discretization of $[0,1]$. Conversely, an algorithm that learns $\alpha$-multicalibrated predictors on the large sets of $\mathcal{C}$ in time $T$ yields a $(\rho,\tau)$-weak agnostic learner for $\mathcal{C}$ in time $T\cdot\mathrm{poly}(1/\tau)$ whenever $\tau \le \min\{\rho - 2\gamma,\ \rho/4 - 4\alpha\}$, so for worst-case targets the computational complexity of multicalibration is governed by weak agnostic learning of $\mathcal{C}$.

## Proof sketch

The residual $y - v$ on the level set $\{p = v\}$ is a labelled distribution on which a violating $c$ has correlation at least $\alpha$, so the weak learner returns a correction direction $h$ with correlation $\mathrm{poly}(\alpha)$, and the potential argument still applies with $h$ in place of $c$. For the converse, given labels $y \in [-1,1]$ for which some set of $\mathcal{C}$ has correlation $\rho$, either a constant hypothesis already has correlation $\tau$, or one learns a predictor $x$ that is multicalibrated for the labels with respect to $\mathcal{C} \cup \{X\}$ and returns $h = \mathrm{sgn}(x)$, whose correlation with the labels is large because $x$ is calibrated on the whole domain and multiaccurate on the correlated set.

## Depends on

- [Learners and agnostic PAC learnability](../pac-learning/agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Multicalibrated predictors](multicalibrated-predictor.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)

## Proof depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513, Definition 4.1, Theorems 4.2 and 4.4.
- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389, Theorem 9.2.
