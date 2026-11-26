# Bounded proper scoring rules are mixtures of V-shaped elementary scoring rules

For a threshold $\theta \in [0,1]$ let the **V-shaped** (elementary) scoring rule be $S_\theta(p, y) = (\theta - y)\,\mathrm{sign}(p - \theta)$, the loss of an agent who takes action $1$ when the forecast exceeds $\theta$ and whose utility difference between the two actions is $y - \theta$. Every proper scoring rule $S(p, y)$ for binary outcomes with values in $[-1,1]$ can be written, up to terms not depending on $p$, as $S(p,y) = \int_0^1 S_\theta(p, y)\,d\nu(\theta)$ for a nonnegative measure $\nu$ of total mass at most a constant. Consequently the U-calibration error of a sequence of forecasts is, up to a constant factor, the supremum over thresholds $\theta$ of the regret of the forecasts under $S_\theta$.

## Proof sketch

By the Savage–Schervish characterization, the expected score of a proper scoring rule is a convex function $G$ of the forecast and $S(p,y) = G(p) + G'(p)(y - p)$ up to sign conventions; writing $G$ as an integral of hinge functions $\max(p - \theta, 0)$ against the measure $G''$ expresses $S$ as an integral of the elementary rules, and boundedness of $S$ bounds the total mass of $G''$. Regret is subadditive in the scoring rule, so with bounded total mass of $G''$ the U-calibration error is controlled up to a constant factor by the supremum of regret over the elementary rules $S_\theta$.

## Depends on

- [U-calibration error](u-calibration-error.md)
- [Scoring rules and properness for finite outcomes](../../../GameTheory/mechanism-design/remaining-clauses-of-scoring-rules-and-properness.md)

## Proof depends on

- [Characterization of proper scoring rules](../../../GameTheory/mechanism-design/characterization-of-proper-scoring-rules.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168.
