# Multicalibrated predictors

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Assume $p$ takes finitely many values. The predictor $p$ is **$\alpha$-multicalibrated** with respect to $\mathcal{C}$ if

$$
\sum_{v \in \mathrm{range}(p)} \Big| \mathbb{E}_{(x,y) \sim D}\big[c(x)\,(y - v)\,\mathbf{1}[p(x) = v]\big] \Big| \le \alpha \quad \text{for every } c \in \mathcal{C},
$$

that is, $p$ is multiaccurate with respect to $\mathcal{C}$ on every level set of $p$ simultaneously, with the errors on the level sets added up. Taking $\mathcal{C} = \{1\}$ recovers (weighted $\ell_1$) calibration $\mathbb{E}\,\big|\mathbb{E}[y \mid p(x)] - p(x)\big| \le \alpha$; other common variants bound the per-level error relative to $\Pr[p(x) = v]$ or use the $\ell_\infty$ maximum over levels. A relative per-level bound $|\mathbb{E}[c(x)(y - v) \mid p(x) = v]| \le \alpha$ for every level implies the sum above is at most $\alpha$, and the maximum over levels of the summands is within a factor $|\mathrm{range}(p)|$ of their sum. The converse to the relative variant holds only above a mass cutoff: the sum bound $\alpha$ gives relative error at most $\alpha/\eta$ on each level with $\Pr[p(x) = v] \ge \eta$ and nothing on lighter levels, since a level of mass $\eta$ can have relative error $1$ while contributing only $\eta$ to the sum; relative definitions, such as that of Hébert-Johnson, Kim, Reingold and Rothblum, therefore exempt level sets of small mass.

## Depends on

- [Multiaccurate predictors](multiaccurate-predictor.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389.
