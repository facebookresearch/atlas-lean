# Multicalibration implies omniprediction for convex Lipschitz losses

Let $\mathcal{C}$ be a class of real functions on $X$. A convex loss $\ell$ is $(B, \varepsilon)$-nice if there is a closed interval $I_\ell$ on which $\ell(\cdot, y)$ is $B$-Lipschitz for each $y$ and which contains an $\varepsilon$-optimal minimizer of $\ell(\cdot, y)$ for each $y$. A partition $\{S_i\}$ of $X$ is $\alpha$-approximately multicalibrated for $\mathcal{C}$ if $\mathbb{E}_{i}\big|\mathrm{Cov}_{D \mid S_i}[c(x), y]\big| \le \alpha$ for every $c \in \mathcal{C}$, the piece $i$ being drawn with probability $D(S_i)$. If the partition is $\alpha$-approximately multicalibrated, then its canonical predictor $p(x) = \mathbb{E}[y \mid x \in S_i]$ for $x \in S_i$, post-processed by the $I_\ell$-restricted optimal action, is an $(\mathcal{L}(B,\varepsilon), \mathcal{C}, 2\alpha B + \varepsilon)$-omnipredictor for the family $\mathcal{L}(B,\varepsilon)$ of all $(B,\varepsilon)$-nice losses, and an $(\mathcal{L}(B,\varepsilon), \mathrm{Lin}_{\mathcal{C}}(W), 2\alpha BW + \varepsilon)$-omnipredictor against linear combinations of $\mathcal{C}$ with $\ell_1$ weight at most $W$. Multicalibration thereby serves as a solution concept for agnostic boosting, and multigroup versions give omnipredictors for multi-group loss minimization.

## Proof sketch

Fix $\ell$ and $c \in \mathcal{C}$, and on each piece $S_i$ compare $c$ with the constant $\hat c_i = \mathbb{E}[c(x) \mid x \in S_i]$ clipped to $I_\ell$. Because $y$ is binary, $\mathbb{E}[\ell(c(x), y) \mid S_i]$ splits according to $y$, and the small covariance of $c(x)$ and $y$ on $S_i$ means conditioning on $y$ barely changes the distribution of $c(x)$; convexity (Jensen's inequality) and $B$-Lipschitzness then give $\mathbb{E}[\ell(\hat c_i, y) \mid S_i] \le \mathbb{E}[\ell(c(x), y) \mid S_i] + 2B\,|\mathrm{Cov}_{S_i}[c, y]| + \varepsilon$. Since $y$ is $\mathrm{Ber}(p_i)$ on $S_i$, the optimal action $k_\ell(p_i)$ does at least as well as $\hat c_i$, and averaging over pieces gives the bound.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)

## Sources

- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389, Definitions 3.1 and 5.3, Theorem 6.3, Corollaries 6.5 and 6.6.
