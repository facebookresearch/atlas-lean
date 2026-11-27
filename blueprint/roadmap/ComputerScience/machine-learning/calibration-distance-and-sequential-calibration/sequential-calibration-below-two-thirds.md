# Breaking the two-thirds barrier for sequential calibration

In sequential calibration the forecaster fixes a finite set $P \subset [0,1]$, and in each of $T$ rounds forecasts $p_t \in P$ while the adversary chooses $y_t \in \{0,1\}$ without seeing $p_t$; an adaptive adversary may use all past forecasts and outcomes, an oblivious one only past outcomes. There is a forecasting algorithm whose expected $\ell_1$ calibration error $\sum_{p \in P}|m_p - p\,n_p|$ against every adaptive adversary is $O(T^{2/3 - \varepsilon})$ for some absolute constant $\varepsilon > 0$, the first improvement on the $O(T^{2/3})$ bound of Foster and Vohra. Conversely, some oblivious adversary forces every forecaster to incur expected calibration error $\Omega(T^{0.54389})$, the first super-square-root lower bound against oblivious adversaries. Both results go through the equivalence between calibrated forecasting and the sign-preservation game with reuse: lower bounds for the game give lower bounds for calibration and algorithms for the game give forecasting algorithms.

## Proof sketch

The equivalence is bidirectional: if $\mathrm{opt}(n,n) = O(n^{1-\varepsilon})$ then some forecaster has calibration error $O(T^{2/3-\varepsilon/18})$, and if $\mathrm{opt}(n,n^\alpha) = \Omega(n^\beta)$ then some adversary forces calibration error $\tilde\Omega(T^{(\beta+1)/(\alpha+2)})$; forecast values correspond to cells and the signs of the accumulated errors $m_p - p\,n_p$ to the labels. The upper bound $\mathrm{opt}(n,n) = O(n^{1-\varepsilon})$ comes from a recursive strategy for Player-L on the two halves of the board which, after a placement in one half deletes many minus signs in the other, biases its later signs towards minus. The oblivious lower bound comes from an oblivious Player-P strategy in the sign-preservation game with additional structure, transferred through the same reduction.

## Depends on

- [The sign-preservation game](sign-preservation-game.md)

## Proof depends on

- [Calibration error must exceed T to the power 0.528 against adaptive adversaries](calibration-lower-bound-sidestepping.md)

## Sources

- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, R. Kleinberg, P. Okoroafor, "Breaking the T^{2/3} Barrier for Sequential Calibration", STOC (2025), arXiv:2406.13668, Theorems 1.2–1.4.
- D. P. Foster, R. V. Vohra, "Asymptotic Calibration", Biometrika 85 (1998).
