# Block elimination with signed forcing in a Biot-type rate system

Let $n$, $m$ be finite index sets, $K \in \mathbb{R}^{n \times n}$ with a two-sided inverse $K^{-1}$, $Q \in \mathbb{R}^{n \times m}$ and $C, H \in \mathbb{R}^{m \times m}$. If $\dot u \in \mathbb{R}^n$, $\dot p, s, p \in \mathbb{R}^m$ and $\dot f \in \mathbb{R}^n$ satisfy

$$K \dot u + Q \dot p = \dot f, \qquad Q^{\top} \dot u - C \dot p = s - H p,$$

then $\dot u = K^{-1}(\dot f - Q \dot p)$ and $(Q^{\top} K^{-1} Q + C)\, \dot p = Q^{\top} K^{-1} \dot f - s + H p$. (The dots are names of vectors; no differentiation is involved.)

This is an algebraic elimination, and its signs are not those of the physical storage balance. With the left side of the second equation as printed, the dissipative storage balance of Biot consolidation has right-hand side $H p - s$, not $s - H p$: for $Q = 0$, $C = H = I$ and $s = 0$ the system above gives $\dot p = p$, whereas the physical pressure decays, $\dot p = -p$. The physical rate system is the [Biot rate system](../../../EarthScience/hydrology-and-surface-processes/part-02/discretized-biot-consolidation/satisfies-biot-rate-system.md).

## Sources

- M. A. Biot, General theory of three-dimensional consolidation, *J. Appl. Phys.* 12 (1941).
