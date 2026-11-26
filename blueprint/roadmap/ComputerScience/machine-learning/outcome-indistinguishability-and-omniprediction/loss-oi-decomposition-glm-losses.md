# Loss OI decomposes into calibration plus multiaccuracy and yields omnipredictors for GLM losses

For every family of losses $\mathcal{L}$ and hypothesis class $\mathcal{C}$, $\varepsilon$-loss OI implies $(\mathcal{L}, \mathcal{C}, \varepsilon)$-omniprediction, and loss OI is equivalent to calibration together with multiaccuracy for a class of functions derived from the derivatives of the losses composed with the hypotheses. For the convex losses arising from generalized linear models (squared loss, logistic loss and other matching losses), calibrated multiaccuracy with respect to $\mathcal{C}$ implies loss OI without full multicalibration, and for these losses loss OI is equivalent to a geometric indistinguishability formulated as Pythagorean theorems in the associated Bregman divergence. Calibrated multiaccuracy can be achieved with computational cost comparable to multiaccuracy.

## Proof sketch

Loss OI implies omniprediction because under simulated outcomes the action $k_\ell(p(x))$ is optimal pointwise, and indistinguishability transfers the inequality to Nature. For a matching loss with link $\psi$, $\ell(c(x), y) - \ell(k_\ell(p(x)), y)$ is affine in $y$ with slope depending on $c(x)$ and $p(x)$, so its distinguishing advantage splits into a multiaccuracy term $\mathbb{E}[c(x)(y - p(x))]$ and a calibration term $\mathbb{E}[\psi(p(x))(y - p(x))]$; the Pythagorean identity expresses the same split in Bregman divergence.

## Depends on

- [Loss outcome indistinguishability and calibrated multiaccuracy](loss-oi-and-calibrated-multiaccuracy.md)
- [Omnipredictors](omnipredictor.md)
- [Multiaccurate predictors](../multicalibration-and-multiaccuracy/multiaccurate-predictor.md)

## Sources

- P. Gopalan, L. Hu, M. P. Kim, O. Reingold, U. Wieder, "Loss Minimization through the Lens of Outcome Indistinguishability", ITCS (2023), arXiv:2210.08649.
