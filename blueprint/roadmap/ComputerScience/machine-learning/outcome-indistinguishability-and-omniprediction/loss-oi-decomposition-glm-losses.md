# Loss OI decomposes into calibration plus multiaccuracy and yields omnipredictors for GLM losses

For every family of losses $\mathcal{L}$ and hypothesis class $\mathcal{C}$, $\varepsilon$-loss OI implies $(\mathcal{L}, \mathcal{C}, \varepsilon)$-omniprediction, and it is not equivalent to omniprediction. Loss OI splits into hypothesis OI, which is equivalent to multiaccuracy for the class $\partial\mathcal{L} \circ \mathcal{C} = \{\partial\ell \circ c\}$ of discrete derivatives $\partial\ell(t) = \ell(t,1) - \ell(t,0)$ composed with the hypotheses, and decision OI, which calibration implies; hence $\varepsilon$-calibration together with $(\partial\mathcal{L} \circ \mathcal{C}, \varepsilon)$-multiaccuracy implies $(\mathcal{L}, \mathcal{C}, O(\varepsilon))$-loss OI. For the convex losses arising from generalized linear models (squared loss, logistic loss and other matching losses), calibrated multiaccuracy with respect to $\mathcal{C}$ implies loss OI without full multicalibration, and for these losses loss OI is equivalent to a geometric indistinguishability formulated as Pythagorean theorems in the associated Bregman divergence. Calibrated multiaccuracy can be achieved with computational cost comparable to multiaccuracy.

## Proof sketch

Loss OI implies omniprediction because under simulated outcomes the action $k_\ell(p(x))$ is optimal pointwise, and indistinguishability transfers the inequality to Nature. Every test $\ell(c(x), y) - \ell(k_\ell(p(x)), y)$ is affine in $y$, so its advantage is $\mathbb{E}[(\partial\ell(c(x)) - \partial\ell(k_\ell(p(x))))(y - p(x))]$, a multiaccuracy term for $\partial\ell \circ c$ minus a weighted calibration term. For a matching loss $\ell_g(t, y) = g(t) - yt$ of a GLM with increasing transfer function $g'$, $\partial\ell_g(t) = -t$, so $\partial\mathcal{L} \circ \mathcal{C} = -\mathcal{C}$ and multiaccuracy for $\mathcal{C}$ itself suffices; the remaining term $\mathbb{E}[k_\ell(p(x))(y - p(x))]$, with $k_\ell = (g')^{-1}$, is controlled by calibration. The Pythagorean identity expresses the same split in the Bregman divergence of $g$.

## Depends on

- [Loss outcome indistinguishability and calibrated multiaccuracy](loss-oi-and-calibrated-multiaccuracy.md)
- [Omnipredictors](omnipredictor.md)
- [Multiaccurate predictors](../multicalibration-and-multiaccuracy/multiaccurate-predictor.md)

## Sources

- P. Gopalan, L. Hu, M. P. Kim, O. Reingold, U. Wieder, "Loss Minimization through the Lens of Outcome Indistinguishability", ITCS (2023), arXiv:2210.08649, Propositions 1 and 2, Theorems 4.9, 5.3 and 5.5.
