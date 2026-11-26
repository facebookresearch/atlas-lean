# The sign-preservation game

The **sign-preservation game** of Qiao and Valiant is a two-player game abstracting online calibration. A state is a vector of integer counters indexed by a finite grid of forecast values; in each round the forecaster selects a grid value $v$ (possibly at random) and the adversary then increments or decrements the counter at $v$ by an amount corresponding to the calibration discrepancy $y - v$, and the forecaster is penalized when it selects a value whose counter has the "wrong" sign relative to the side of $v$ (so that predicting $v$ there would increase the calibration error). In the variant **with reuse** (SPR), the forecaster may additionally return to previously used values under specified rules. Game values of both versions translate into bounds on the minimax $\ell_1$ calibration error.

## Depends on

- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- M. Qiao, G. Valiant, "Stronger Calibration Lower Bounds via Sidestepping", STOC (2021), arXiv:2012.03454.
- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, R. Kleinberg, P. Okoroafor, "Breaking the T^{2/3} Barrier for Sequential Calibration", STOC (2025), arXiv:2406.13668.
