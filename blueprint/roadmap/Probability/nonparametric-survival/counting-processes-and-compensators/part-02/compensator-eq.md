# Compensator as hazard mass up to the observed time

In the random-censorship model, a subject has latent failure time $T$ and censoring time $C$ on a measurable space, observed time $X = \min(T, C)$, counting process $N(t) = \mathbf 1\{T \le C, T \le t\}$, censoring process $N^c(t) = \mathbf 1\{C < T, C \le t\}$ and at-risk process $Y(t) = \mathbf 1\{t \le X\}$. For a hazard measure $\Lambda$, the compensator $A(t) = \int_{(-\infty, t]}Y\,d\Lambda$ equals the mass $\Lambda\big((-\infty, \min(t, X)]\big)$, computed in $[0, \infty]$, with an infinite mass read as $A(t) = 0$.
