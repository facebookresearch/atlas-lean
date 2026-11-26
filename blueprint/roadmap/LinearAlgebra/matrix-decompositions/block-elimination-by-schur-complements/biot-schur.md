# Schur-complement reduction of the Biot consolidation system

Let $n$, $m$ be finite index sets, $K \in \mathbb{R}^{n \times n}$ with a two-sided inverse $K^{-1}$ ($K K^{-1} = K^{-1} K = I$), $Q \in \mathbb{R}^{n \times m}$ and $C \in \mathbb{R}^{m \times m}$. If $u \in \mathbb{R}^n$, $p \in \mathbb{R}^m$ satisfy

$$K u + Q p = f, \qquad Q^{\top} u - C p = g,$$

then $u = K^{-1}(f - Q p)$ and $(Q^{\top} K^{-1} Q + C)\, p = Q^{\top} K^{-1} f - g$.

The rate form of the Biot equations is the case $g = s - H p$ for rate vectors $\dot u, \dot p, \dot f$ in place of $u, p, f$ (the dots are names of vectors; no differentiation is involved): from $K \dot u + Q \dot p = \dot f$ and $Q^{\top} \dot u - C \dot p = s - H p$ follow $\dot u = K^{-1}(\dot f - Q \dot p)$ and $(Q^{\top} K^{-1} Q + C)\, \dot p = Q^{\top} K^{-1} \dot f - s + H p$. Its signs are not those of the physical storage balance: with the left side as printed, the dissipative storage balance of Biot consolidation has right-hand side $H p - s$; for $Q = 0$, $C = H = I$ and $s = 0$ the signed system gives $\dot p = p$, whereas the physical pressure decays, $\dot p = -p$. The physical rate system is the [Biot rate system](../../../EarthScience/hydrology-and-surface-processes/part-02/discretized-biot-consolidation/satisfies-biot-rate-system.md).

## Sources

- M. A. Biot, General theory of three-dimensional consolidation, *J. Appl. Phys.* 12 (1941).
