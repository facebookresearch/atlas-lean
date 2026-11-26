# Oracle-efficient online multicalibration and omniprediction

In the online adversarial setting, where contexts and outcomes are chosen by an adversary and the forecaster predicts $p_t \in [0,1]$ each round, there is an algorithm that achieves online multicalibration with respect to infinite benchmark classes $F$ using calls to an offline (batch) optimization oracle for $F$ rather than enumerating $F$, and consequently online omniprediction (sublinear excess loss against the best $f \in F$ for every loss in a convex Lipschitz family, the loss being chosen after the predictions) and swap omniprediction. Previous online multicalibration algorithms required enumerating every $f \in F$ each round and therefore only applied to small finite classes.

## Proof sketch

The forecaster plays a game against an adversary choosing a pair (benchmark function, forecast bucket), and uses a follow-the-perturbed-leader style reduction so that each round requires one oracle call for the adversary's best response. Online multicalibration follows from the no-regret property of the adversary dynamics, and online omniprediction is derived from online multicalibration exactly as in the batch argument, applied to empirical averages.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Swap agnostic learning and swap omniprediction](swap-agnostic-learning.md)

## Proof depends on

- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)
- [Regularized Follow-the-Leader / Online Mirror Descent regret](../online-learning-and-boosting/regularized-follow-the-leader-online-mirror-descent-regret.md)
- [Multicalibration as multi-objective learning via game dynamics](../multicalibration-and-multiaccuracy/multicalibration-game-dynamics.md)

## Sources

- S. Garg, C. Jung, O. Reingold, A. Roth, "Oracle Efficient Online Multicalibration and Omniprediction", SODA (2024), arXiv:2307.08999.
