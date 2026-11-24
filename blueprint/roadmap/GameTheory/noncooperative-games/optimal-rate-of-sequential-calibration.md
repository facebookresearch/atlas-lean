# Optimal rate of sequential calibration

Determine the minimax rate of cumulative calibration error in the forecaster-versus-adversary game. This connects prediction, learning, and equilibrium concepts.

## What would settle it

Fix the forecast grid/randomization and the adversary's information, especially whether the realized forecast is observed. Prove matching upper and lower bounds for expected L1 calibration error after T rounds. Do not assume a pure power law exists before proving it.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status.

Dagan, Daskalakis, Fishelson and Golowich give a forecaster with calibration error O(T^{2/3−ε}) for some ε > 0 and a lower bound Ω(T^{0.54389}); Dai and Fishelson (preprint) make the improvement explicit. The two exponents remain apart in these works.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- Yuval Dagan et al., *Breaking the T^(2/3) Barrier for Sequential Calibration*, arXiv:2406.13668v4 (2026), abstract and §1. <https://arxiv.org/abs/2406.13668v4>
- Eric Dai and Maxwell Fishelson, *Explicit Asymptotic Bounds for Sequential Calibration Beyond T^(2/3)*, arXiv:2610.07623v2 (2026), abstract. <https://arxiv.org/abs/2610.07623v2>
