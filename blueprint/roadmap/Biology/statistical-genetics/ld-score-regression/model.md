# Random-effects model of LD-score regression

The random-effects model of LD-score regression (Bulik-Sullivan et al. 2015), stated at
the level of raw second moments, for `N` individuals and `M` markers with heritability `h2`.

* `beta k` is the (random) effect of marker `k`, with `∫ β k * β l = h2 / M * [k = l]`;
* `eps i` is the environmental noise of individual `i`, with
  `∫ ε i * ε i' = (1 - h2) * [i = i']`;
* effects and noise are orthogonal in `L²`.

The measure is arbitrary and no means are assumed; for a probability measure and mean-zero
effects and noise these are the covariance conditions of the cited model. The genotype matrix is
not part of the model: all expectations are conditional on it.
