# Strong existence and pathwise uniqueness for scalar Lipschitz SDEs

Let $B$ be real Brownian motion under $P$, adapted to $(\mathcal F_t)$, with increments $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Assume each $\mathcal F_t$ contains every $P$-null set. Let $\sigma,b:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $K\ge0$, and fix a deterministic $x\in\mathbb R$.

There exists a real process $Y$ on this same probability space and filtration, adapted and continuous on every path, with finite integrated second moment on every finite horizon, such that for each fixed $t\ge0$, almost surely,

$$Y_t=x+\int_0^t\sigma(Y_s)\,dB_s+\int_0^t b(Y_s)\,ds.$$

The stochastic term is the actual Itô integral. For every $0\le t\le T$ the same solution satisfies

$$\mathbb E\sup_{0\le s\le t}|Y_s|^2
\le \left[3x^2+\bigl(24\sigma(0)^2+6T b(0)^2\bigr)T\right]
\exp\bigl((24+6T)K^2t\bigr).$$

If $Z$ is any other adapted, every-path continuous solution with locally finite integrated second moment and the same fixed-time almost-sure integral equation, coefficients, initial value and Brownian driver, then $Y$ and $Z$ are indistinguishable: outside one null set, $Y_t=Z_t$ for every $t\ge0$.

No pre-existing solution or convergence hypothesis is assumed. Completeness is sufficient for this construction, not claimed necessary; right continuity of the filtration is not required. The fixed-time equation and the common-event uniqueness statement have different quantifier orders. Expectations above are nonnegative extended integrals.

Actual Picard iterates converge uniformly on each finite horizon almost surely and in mean-square supremum norm. Lipschitz estimates pass both actual integrals to the limit; uniqueness of limits in measure identifies the equation. The maximal-moment bound and pathwise uniqueness then apply to that constructed solution. This is the scalar autonomous case of Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3, with the complete-filtration convention in Definition 8.1.
