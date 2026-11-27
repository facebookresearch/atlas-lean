# Minimax lower bounds

Lower bounds on the minimax risk $\inf_{\hat\theta} \sup_\theta \mathbb{E}_\theta\, \ell(\theta, \hat\theta)$, the infimum running over randomised estimators, obtained by reducing estimation to testing. Le Cam's two-point method bounds the risk below by $\ell(\theta_0, \theta_1)(1 - \mathrm{TV}(P_{\theta_0}, P_{\theta_1}))/(2\alpha)$ for a loss with the $\alpha$-triangle inequality, and Pinsker's inequality turns the total variation into a Kullback–Leibler divergence, which tensorizes over i.i.d. samples. Assouad's lemma sums such bounds over the coordinates of a hypercube of parameters. Fano's method extends the reduction to many separated hypotheses, and Le Cam–Birgé and Scheffé tournaments build estimators from pairwise tests that attain matching upper rates.

- [Assouad's lemma](mul-one-sub-le-minimax.md)
- [Assouad's lemma for one deterministic estimator](mul-one-sub-le-four-mul-i-sup.md)
- [Measurable choice of a minimiser](exists-measurable-argmin.md)
- [Le Cam's two-point bound with Pinsker's inequality](mul-one-sub-sqrt-kl-div-le-minimax.md)
- [Le Cam's two-point lower bound](mul-one-sub-total-variation-dist-le-mini.md)
- [Le Cam's two-point lower bound for one deterministic estimator](mul-one-sub-total-variation-dist-le-two.md)
- [Fano and Two-Point Minimax Rates](fano-and-two-point-minimax-rates/README.md)
- [Robust Hypothesis Selection](robust-hypothesis-selection/README.md)

## Related topics

- [Total variation and Pinsker's inequality](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/README.md)
- [Fano's inequality](../../../InformationTheory/information-inequalities/fano-s-inequality/README.md)
- [Contiguity and Le Cam's lemmas](../contiguity-and-le-cam-s-lemmas/README.md)
