# Swap omniprediction, swap multicalibration and swap agnostic learning are equivalent

For every class $\mathcal{C}$ and the family of convex Lipschitz losses, the following are equivalent up to polynomial changes of the error parameter: swap omniprediction, swap multicalibration with respect to $\mathcal{C}$, and swap agnostic learning for every convex loss. Moreover swap multicalibration is essentially equivalent to standard multicalibration, so existing multicalibration algorithms achieve all three. In particular multigroup fairness in the form of multicalibration is necessary, not merely sufficient, for the swap variant of omniprediction, and a single notion of outcome indistinguishability captures all existing notions of omniprediction and multicalibration.

## Proof sketch

Swap multicalibration implies swap omniprediction by applying the omniprediction argument separately on each level set with its own $c_v$. Conversely, a violation of multicalibration on a level set yields, for the squared loss, a better hypothesis on that level set, contradicting swap omniprediction; this shows necessity. Swap multicalibration follows from multicalibration because the adversary's per-level choice can be absorbed into the level-set sum in the definition.

## Depends on

- [Swap agnostic learning and swap omniprediction](swap-agnostic-learning.md)
- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)
- [Loss OI decomposes into calibration plus multiaccuracy and yields omnipredictors for GLM losses](loss-oi-decomposition-glm-losses.md)

## Proof depends on

- [Swap agnostic learning and swap omniprediction](swap-agnostic-learning.md)
- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)
- [Loss OI decomposes into calibration plus multiaccuracy and yields omnipredictors for GLM losses](loss-oi-decomposition-glm-losses.md)

## Sources

- P. Gopalan, M. P. Kim, O. Reingold, "Swap Agnostic Learning, or Characterizing Omniprediction via Multicalibration", arXiv:2302.06726 (2023).
