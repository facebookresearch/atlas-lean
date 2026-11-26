# Sublinear U-calibration characterizes forecasts that are good for every agent and is achievable at square-root rate

Sublinear U-calibration error is necessary and sufficient for every agent with a bounded utility who best responds to the forecasts to have sublinear (external) regret. Optimizing the forecasts for a single scoring rule, such as the Brier score, does not guarantee sublinear regret for all agents, whereas calibrated forecasts do, but calibration is not necessary and calibrated forecasting has provably worse convergence rates. There is an online algorithm with expected U-calibration error $O(\sqrt{T})$ against adaptive adversaries, bypassing the super-$\sqrt{T}$ lower bounds for $\ell_1$ calibration error, and the U-calibration error of a given sequence is computable efficiently.

## Proof sketch

Every bounded proper scoring rule is a mixture of V-shaped elementary scoring rules $S_\theta(p, y)$, one per threshold $\theta$, so the supremum over scoring rules equals, up to constants, the supremum over thresholds of the regret of the threshold agent, which is a one-parameter family. An online algorithm with $O(\sqrt{T})$ regret simultaneously for all thresholds, obtained by randomizing over a grid and using the structure of V-shaped losses, gives the upper bound.

## Depends on

- [U-calibration error](u-calibration-error.md)
- [Best responding to calibrated forecasts gives no swap regret](calibrated-forecasts-best-response-swap-regret.md)

## Proof depends on

- [U-calibration error](u-calibration-error.md)
- [Best responding to calibrated forecasts gives no swap regret](calibrated-forecasts-best-response-swap-regret.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168.
