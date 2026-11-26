# Omnipredictors

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). For a loss $\ell : \mathbb{R} \times \{0,1\} \to \mathbb{R}$ let $k_\ell(v) \in \arg\min_t \mathbb{E}_{y \sim \mathrm{Ber}(v)}[\ell(t, y)]$ be the optimal action for a forecast $v$, a univariate data-independent post-processing. For a family of losses $\mathcal{L}$ and a hypothesis class $\mathcal{C}$ of functions $X \to \mathbb{R}$, $p$ is an **$(\mathcal{L}, \mathcal{C}, \varepsilon)$-omnipredictor** if for every $\ell \in \mathcal{L}$

$$
\mathbb{E}_{(x,y) \sim D}\big[\ell(k_\ell(p(x)), y)\big] \le \min_{c \in \mathcal{C}} \mathbb{E}_{(x,y) \sim D}\big[\ell(c(x), y)\big] + \varepsilon .
$$

A single predictor thus serves as an agnostic learner for every loss in $\mathcal{L}$ simultaneously, the loss being chosen only after learning.

## Sources

- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389.
