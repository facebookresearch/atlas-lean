# Outcome indistinguishability and its access hierarchy

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Let $\tilde y \sim \mathrm{Ber}(p(x))$ denote outcomes simulated from the predictor. For a class $\mathcal{A}$ of distinguishers, $p$ is **$\varepsilon$-outcome indistinguishable** (OI) if for every $A \in \mathcal{A}$

$$
\Big| \Pr_{(x,y) \sim D}[A(x, y, \cdot) = 1] - \Pr_{x \sim D_X,\, \tilde y \sim \mathrm{Ber}(p(x))}[A(x, \tilde y, \cdot) = 1] \Big| \le \varepsilon .
$$

The hierarchy is indexed by what the distinguisher sees besides an individual $(x, y)$: **no-access OI** (only $(x, y)$), **sample-access OI** (also $p(x)$), **oracle-access OI** (query access to $p$ on arbitrary points), and **code-access OI** (the description of $p$). Distinguishers may also receive several independent samples.

## Depends on

- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- C. Dwork, M. P. Kim, O. Reingold, G. N. Rothblum, G. Yona, "Outcome Indistinguishability", STOC (2021), arXiv:2011.13426.
