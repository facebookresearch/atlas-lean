# Breaking the two-thirds barrier for sequential calibration

There is a forecasting algorithm whose expected $\ell_1$ calibration error against every adaptive adversary over $T$ binary outcomes is $O(T^{2/3 - \varepsilon})$ for some absolute constant $\varepsilon > 0$, the first improvement on the $O(T^{2/3})$ bound of Foster and Vohra. Conversely, an oblivious adversary forces calibration error $\Omega(T^{0.54389})$, the first super-square-root lower bound against oblivious adversaries. Both results go through the equivalence between calibrated forecasting and the sign-preservation game with reuse: lower bounds for the game give lower bounds for calibration and algorithms for the game give forecasting algorithms.

## Proof sketch

The equivalence is bidirectional: a forecaster induces a strategy in the game by tracking the counters of its forecast grid, and a game strategy induces a forecaster by mapping its moves to forecast values together with a fine-grained correction that reuses values. An improved upper bound on the value of the reuse game, obtained by a recursive strategy that balances counters across scales, yields the $T^{2/3 - \varepsilon}$ forecaster; refining the Qiao–Valiant adversary within the reuse game yields the $T^{0.54389}$ lower bound.

## Depends on

- [The sign-preservation game](sign-preservation-game.md)

## Proof depends on

- [Calibration error must exceed T to the power 0.528 against adaptive adversaries](calibration-lower-bound-sidestepping.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, R. Kleinberg, P. Okoroafor, "Breaking the T^{2/3} Barrier for Sequential Calibration", STOC (2025), arXiv:2406.13668.
- D. P. Foster, R. V. Vohra, "Asymptotic Calibration", Biometrika 85 (1998).
