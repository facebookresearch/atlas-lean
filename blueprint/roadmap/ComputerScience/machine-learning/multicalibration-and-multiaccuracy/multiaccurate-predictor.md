# Multiaccurate predictors

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). The predictor $p$ is **$\alpha$-multiaccurate** with respect to $\mathcal{C}$ if

$$
\big| \mathbb{E}_{(x,y) \sim D}\big[c(x)\,(y - p(x))\big] \big| \le \alpha \quad \text{for every } c \in \mathcal{C}.
$$

For $c = \mathbf{1}_S$ this says that the average prediction on the subpopulation $S$ is within $\alpha$ of its average outcome, in the unnormalized sense weighted by $\Pr[x \in S]$.

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
- M. P. Kim, A. Ghorbani, J. Zou, "Multiaccuracy: Black-Box Post-Processing for Fairness in Classification", AIES (2019), arXiv:1805.12317.
