# Low-degree multicalibration

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). For $k \in \mathbb{N}$, the predictor $p$ is **degree-$k$ $\alpha$-multicalibrated** with respect to $\mathcal{C}$ if

$$
\big| \mathbb{E}\big[c(x)\, w(p(x))\, (y - p(x))\big] \big| \le \alpha \quad \text{for all } c \in \mathcal{C} \text{ and all polynomials } w \text{ of degree at most } k \text{ with } \sup_{[0,1]} |w| \le 1 .
$$

Degree $0$ is multiaccuracy, and letting the weight class range over all bounded functions $w$ of $p(x)$ recovers (an $\ell_\infty$-weighted form of) full multicalibration, so the degrees interpolate between the two notions; for $\ell$ classes the definition uses vector-valued predictions and multivariate polynomials.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Sources

- P. Gopalan, M. P. Kim, M. Singhal, S. Zhao, "Low-Degree Multicalibration", COLT (2022), arXiv:2203.01255.
