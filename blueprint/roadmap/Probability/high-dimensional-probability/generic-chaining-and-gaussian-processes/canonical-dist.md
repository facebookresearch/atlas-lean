# Canonical distance of a process

For real functions $(X_t)_{t \in T}$ on a measure space $(\Omega, P)$ (random variables when $P$ is a probability
measure), the canonical distance is $d(s, t) = \|X_s - X_t\|_{L^2(P)} = (\int (X_s - X_t)^2 \, dP)^{1/2}$ (Talagrand, *Upper and Lower Bounds for Stochastic
Processes*, 2nd ed., 2021, (2.113)), taken here with values in $[0, \infty]$ (infinite when $X_s - X_t$ is not square-integrable). It is a
pseudo-distance: distinct indices carrying the same variable are at distance zero. For a centred
Gaussian process it determines the law of the increments, which is why the majorizing measure
theorem is a statement about the metric space $(T, d)$. The
[generic chaining bound for Gaussian processes](integral-i-sup-le-gamma-two-canonical-di.md) and the
[majorizing measure theorem](majorizing-measure.md) are both stated with this distance.
