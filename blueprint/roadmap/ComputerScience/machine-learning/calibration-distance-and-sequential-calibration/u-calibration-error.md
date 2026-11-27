# U-calibration error

For binary outcomes $y_1, \dots, y_T$ and forecasts $p_1, \dots, p_T \in [0,1]$, the **U-calibration error** is the worst-case regret of the forecasts over all bounded proper scoring rules:

$$
\mathrm{UCal}_T = \sup_{S} \Big( \sum_{t=1}^T S(p_t, y_t) - \min_{p \in [0,1]} \sum_{t=1}^T S(p, y_t) \Big),
$$

where the supremum ranges over proper scoring rules (losses) $S : [0,1] \times \{0,1\} \to [-1,1]$; by properness the inner minimum is attained at the base rate $p = \frac1T\sum_t y_t$. For a randomized forecaster the error is taken in expectation. Equivalently, by the correspondence $S(p,y) = -u(a^*(p), y)$ between agents and proper scoring rules, it is the maximal regret, against the best fixed action in hindsight, of an agent with finitely many actions and utilities $u(a,y) \in [-1,1]$ who plays a best response $a^*(p_t)$ to each forecast.

## Depends on

- [Scoring rules and properness for finite outcomes](../../../GameTheory/mechanism-design/remaining-clauses-of-scoring-rules-and-properness.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168, Lemma 3 and equation (9).
