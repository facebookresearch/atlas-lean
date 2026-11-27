# Calibration error must exceed T to the power 0.528 against adaptive adversaries

In online binary forecasting over $T$ rounds, the forecaster fixes a finite set $P \subset [0,1]$ of allowed forecasts, and before each bit $y_t \in \{0,1\}$ is revealed forecasts some $p_t \in P$. The $\ell_1$ calibration error is $\sum_{p \in P} |m_p - p\, n_p|$, with $n_p$ the number of rounds on which $p$ was forecast and $m_p$ the number of ones among them. Let $\alpha = \log 8/\log 255$, $\beta = \log(9/2)/\log 255$ and $c = (2\beta+1)/(\alpha+2\beta+2) > 0.528$. There is a randomized adaptive adversary, choosing each bit from the past bits and forecasts, against which every forecaster has expected calibration error $\Omega(T^c/\sqrt{\log T}) = \Omega(T^{0.528})$. This is the first lower bound improving on the $\Omega(\sqrt{T})$ bound given by independent fair coins.

## Proof sketch

A general reduction shows that if $(\alpha,\beta)$ is admissible, meaning that Player A can preserve $\Omega(k^\beta)$ signs in the sign-preservation game with $k$ cells and $k^\alpha$ rounds, then some adversary forces expected calibration error $\Omega(T^{(2\beta+1)/(\alpha+2\beta+2)}/\sqrt{\log T})$; the value $\mathrm{opt}(255, 8) = 8$ shows the stated pair is admissible. The adversary uses two techniques. Early stopping: it suffices to make the calibration error large at some intermediate time, since the adversary can then switch to a sequence that keeps it large. Sidestepping: after a stretch of coins with bias $p$, the adversary moves to a bias on the same side of $p$ as the sign of the accumulated error $m_p - p\,n_p$, so that the error from earlier forecasts cannot be covered up later. Forecast values play the role of cells, and errors that cannot be covered up play the role of preserved signs.

## Proof depends on

- [The sign-preservation game](sign-preservation-game.md)

## Sources

- M. Qiao, G. Valiant, "Stronger Calibration Lower Bounds via Sidestepping", STOC (2021), arXiv:2012.03454, Theorems 1 and 4.
