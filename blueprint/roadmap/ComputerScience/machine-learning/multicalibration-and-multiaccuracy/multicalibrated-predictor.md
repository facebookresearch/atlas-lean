# Multicalibrated predictors

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Assume $p$ takes finitely many values. The predictor $p$ is **$\alpha$-multicalibrated** with respect to $\mathcal{C}$ if

$$
\sum_{v \in \mathrm{range}(p)} \Big| \mathbb{E}_{(x,y) \sim D}\big[c(x)\,(y - v)\,\mathbf{1}[p(x) = v]\big] \Big| \le \alpha \quad \text{for every } c \in \mathcal{C},
$$

that is, $p$ is multiaccurate with respect to $\mathcal{C}$ on every level set of $p$ simultaneously, with the errors on the level sets added up. Taking $\mathcal{C} = \{1\}$ recovers (weighted $\ell_1$) calibration $\mathbb{E}\,\big|\mathbb{E}[y \mid p(x)] - p(x)\big| \le \alpha$; other common variants bound the per-level error relative to $\Pr[p(x) = v]$ or use the $\ell_\infty$ maximum over levels, and they are polynomially related.

## Depends on

- [Multiaccurate predictors](multiaccurate-predictor.md)
- [Calibration of predictors and the calibrated-LM hallucination lower bound](../transformers-and-language-models/calibration-of-predictors-and-the-calibrated-lm-hallucinatio.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389.
