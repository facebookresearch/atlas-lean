# Calibration error must exceed T to the power 0.528 against adaptive adversaries

In online binary forecasting with $\ell_1$ calibration error $\sum_p |m_p - p\, n_p|$ (summed over the distinct forecast values $p$, with $n_p$ the number of rounds on which $p$ was forecast and $m_p$ the number of ones among them), every forecaster has expected calibration error $\Omega(T^{0.528})$ against some adaptive adversary over $T$ rounds. This is the first lower bound improving on the $\Omega(\sqrt{T})$ bound given by independent fair coins.

## Proof sketch

A general reduction translates lower bounds on the value of the sign-preservation game into calibration lower bounds. The adversary uses two techniques: early stopping, which halts the sequence once the forecaster has committed to forecasts whose counters cannot be repaired, and sidestepping, which steers the outcomes so that the forecaster's natural corrections move counters across zero in the wrong direction. Their combination forces a super-square-root accumulation of discrepancy.

## Proof depends on

- [The sign-preservation game](sign-preservation-game.md)

## Sources

- M. Qiao, G. Valiant, "Stronger Calibration Lower Bounds via Sidestepping", STOC (2021), arXiv:2012.03454.
