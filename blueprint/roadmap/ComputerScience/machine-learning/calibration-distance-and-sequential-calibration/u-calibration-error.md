# U-calibration error

For binary outcomes $y_1, \dots, y_T$ and forecasts $p_1, \dots, p_T \in [0,1]$, the **U-calibration error** is the worst-case regret of the forecasts over all bounded proper scoring rules:

$$
\mathrm{UCal}_T = \sup_{S} \Big( \sum_{t=1}^T S(p_t, y_t) - \min_{p \in [0,1]} \sum_{t=1}^T S(p, y_t) \Big),
$$

where the supremum ranges over proper scoring rules (losses) $S$ with values in $[-1,1]$. Equivalently, by the characterization of proper scoring rules, it is the maximal regret of an agent with an arbitrary bounded utility who best responds to the forecasts, against the best fixed action in hindsight.

## Depends on

- [Characterization of proper scoring rules](../../../GameTheory/mechanism-design/characterization-of-proper-scoring-rules.md)
- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168.
