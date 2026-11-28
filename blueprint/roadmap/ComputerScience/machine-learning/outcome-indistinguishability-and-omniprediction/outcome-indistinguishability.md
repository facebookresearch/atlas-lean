# Outcome indistinguishability and its access hierarchy

Let $D$ be Nature's distribution over $X \times \{0,1\}$, with marginal $D_X$ and Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, and let $p : X \to [0,1]$ be a predictor. Let $\tilde y \sim \mathrm{Ber}(p(x))$ denote outcomes simulated from the predictor. For a class $\mathcal{A}$ of distinguishers, $p$ is **$\varepsilon$-outcome indistinguishable** (OI) if for every $A \in \mathcal{A}$

$$
\Big| \Pr_{(x,y) \sim D}[A(x, y, \cdot) = 1] - \Pr_{x \sim D_X,\, \tilde y \sim \mathrm{Ber}(p(x))}[A(x, \tilde y, \cdot) = 1] \Big| \le \varepsilon .
$$

The hierarchy is indexed by what the distinguisher sees besides an individual $(x, y)$: **no-access OI** (only $(x, y)$), **sample-access OI** (also $p(x)$), **oracle-access OI** (query access to $p$ on arbitrary points), and **code-access OI** (the description of $p$). Here "$\cdot$" stands for this extra access to $p$, and the distinguishers may be randomized; distinguishers may also receive several independent samples.

## Sources

- C. Dwork, M. P. Kim, O. Reingold, G. N. Rothblum, G. Yona, "Outcome Indistinguishability", STOC (2021), arXiv:2011.13426, Definitions 2.1–2.7.
