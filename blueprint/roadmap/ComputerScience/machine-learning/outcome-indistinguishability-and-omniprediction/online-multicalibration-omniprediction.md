# Oracle-efficient online multicalibration and omniprediction

In the online adversarial setting, where contexts and outcomes are chosen by an adversary and the forecaster predicts $p_t \in [0,1]$ each round, there is an algorithm that achieves online ($\ell_2$-swap) multicalibration with respect to infinite benchmark classes $F$ by an efficient reduction to an online squared-loss regression oracle for $F$ (a no-external-regret learner for the squared loss against $F$) rather than by enumerating $F$, against adaptive adversaries; consequently it is an online omnipredictor (sublinear excess loss against the best $f \in F$ for every Lipschitz convex loss, the loss being chosen after the predictions) and in fact a swap omnipredictor. For bounded-norm linear functions, where efficient regression oracles exist, the rates are $O(T^{-1/4})$ for multicalibration and $O(T^{-1/8})$ for omniprediction. Previous online multicalibration algorithms required enumerating every $f \in F$ each round and therefore only applied to small finite classes. In the other direction, some adaptive adversary forces expected swap-omniprediction error $\Omega(T^{-0.472})$ against convex Lipschitz losses for every forecaster (a lower bound on the expectation over the transcript), while a non-oracle-efficient algorithm attains, with probability $1-\rho$, omniprediction at rate $\tilde O(T^{-1/2})$ for finite Boolean classes against all bi-monotone losses bounded in $[-1,1]$ (losses $\ell(y, t)$ monotone in $t$ in opposite directions for $y = 0$ and $y = 1$), which the authors present as an online separation between the rates obtainable for omniprediction and swap omniprediction.

## Proof sketch

Multicalibration with respect to a class closed under affine transformations is characterized by a swap-regret condition: on each level set of the forecast, no $f \in F$ has smaller squared error than the forecast. The algorithm obtains this contextual swap regret by keeping a copy of the regression oracle for each (discretized) forecast value and advancing only the copy whose value is played, adapting the external-to-swap reductions of Blum–Mansour and Ito; the characterization then gives $\ell_2$-swap multicalibration, and omniprediction follows as in the batch argument applied to empirical averages. The lower bound transfers the Qiao–Valiant calibration lower bound.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Swap agnostic learning and swap omniprediction](swap-agnostic-learning.md)

## Proof depends on

- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)
- [Calibration error must exceed T to the power 0.528 against adaptive adversaries](../calibration-distance-and-sequential-calibration/calibration-lower-bound-sidestepping.md)

## Sources

- S. Garg, C. Jung, O. Reingold, A. Roth, "Oracle Efficient Online Multicalibration and Omniprediction", SODA (2024), arXiv:2307.08999, Theorems 1.1–1.4, Section 3, Corollaries 5.2 and 5.3.
