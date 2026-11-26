# Omnipredictors for constrained loss minimization

Omniprediction extends to constrained loss minimization: there are predictors which can be post-processed to minimize any loss from a rich family subject to constraints from a family (for example, group-wise fairness constraints such as statistical parity or equal opportunity across subpopulations), competing with the best hypothesis of $\mathcal{C}$ that satisfies the constraints, as long as the subpopulations used to define the constraints are identifiable by the class. Such omnipredictors exist and are implied by multicalibration with respect to a class augmented by the constraint-defining groups; the post-processing then depends on the group membership and the prediction, not only on the prediction.

## Proof sketch

Lagrangian duality turns the constrained problem into an unconstrained one with a loss that depends on the group through the multipliers; multicalibration with respect to the augmented class makes the predictor indistinguishable from Nature for every such Lagrangian loss, and the omniprediction argument applies to each. The dual variables are chosen after learning, which is why the constraint-defining groups must be included in the multicalibration class.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)
- [Group fairness criteria for scores and classifiers](../algorithmic-fairness/group-fairness-criteria-for-scores-and-classifiers.md)

## Proof depends on

- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)

## Sources

- L. Hu, I. Livni-Navon, O. Reingold, C. Yang, "Omnipredictors for Constrained Optimization", ICML (2023), arXiv:2209.07463.
