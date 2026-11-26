# Black-box post-processing to multiaccuracy preserves accurate subgroups

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Let $p_0$ be any initial predictor and run the multiaccuracy correction procedure (repeatedly find $c \in \mathcal{C}$ with $|\mathbb{E}[c(x)(y - p(x))]| > \alpha$ using a small labelled audit set, and update $p$ multiplicatively in log-odds space in direction $c$). The procedure converges after $O(1/\alpha^2)$ updates to an $\alpha$-multiaccurate predictor, its squared error relative to $p^*$ never increases, and if $p_0$ is already accurate on a subgroup $S$ that is identifiable by $\mathcal{C}$, then the post-processed predictor remains accurate on $S$. The procedure needs only black-box access to $p_0$, not its training data or architecture.

## Proof sketch

Each update is a step along $c$ that decreases a convex potential (the expected squared error, or the cross-entropy in the log-odds parametrization) by $\Omega(\alpha^2)$, which bounds the number of updates. Accuracy on an identifiable subgroup is preserved because updates are triggered only by correlations of the residual with functions in $\mathcal{C}$, and on a subgroup where the residual is already small, no update can increase the subgroup error beyond the audit tolerance.

## Depends on

- [Multiaccurate predictors](multiaccurate-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)

## Sources

- M. P. Kim, A. Ghorbani, J. Zou, "Multiaccuracy: Black-Box Post-Processing for Fairness in Classification", AIES (2019), arXiv:1805.12317.
