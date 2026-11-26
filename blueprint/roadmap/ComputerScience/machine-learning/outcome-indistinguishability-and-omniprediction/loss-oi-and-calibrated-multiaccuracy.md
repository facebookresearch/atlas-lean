# Loss outcome indistinguishability and calibrated multiaccuracy

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). For losses $\mathcal{L}$ and hypotheses $\mathcal{C}$, $p$ is **loss outcome indistinguishable** ($\varepsilon$-loss OI) if for every $\ell \in \mathcal{L}$ and $c \in \mathcal{C}$ the test $(x,y) \mapsto \ell(c(x), y) - \ell(k_\ell(p(x)), y)$ has nearly the same expectation under Nature's outcomes and under simulated outcomes $\tilde y \sim \mathrm{Ber}(p(x))$, up to $\varepsilon$. The predictor is **$\alpha$-calibrated multiaccurate** with respect to $\mathcal{C}$ if it is $\alpha$-calibrated and $\alpha$-multiaccurate with respect to the class $\{x \mapsto c(x)\} \cup \{x \mapsto \phi(p(x))\, \}$ for the relevant derived functions — a notion strictly between multiaccuracy and multicalibration.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Multiaccurate predictors](../multicalibration-and-multiaccuracy/multiaccurate-predictor.md)

## Sources

- P. Gopalan, L. Hu, M. P. Kim, O. Reingold, U. Wieder, "Loss Minimization through the Lens of Outcome Indistinguishability", ITCS (2023), arXiv:2210.08649.
