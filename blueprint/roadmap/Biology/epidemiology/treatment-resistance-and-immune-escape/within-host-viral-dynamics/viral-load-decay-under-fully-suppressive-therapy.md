# Viral load decay under fully suppressive therapy

In the [basic viral dynamics model](basic-viral-dynamics-model-and-its-reproductive-number.md), suppose therapy starting at $t = 0$ blocks all new infections ($\beta = 0$ for $t \ge 0$) and that the virus is at quasi-steady state when therapy starts, $k I(0) = c V(0)$. Write $V_0 = V(0)$ and assume $c \ne d_I$. Then for $t \ge 0$

$$I(t) = I(0)\, e^{-d_I t}, \qquad V(t) = V_0\, \frac{c\, e^{-d_I t} - d_I\, e^{-c t}}{c - d_I}.$$

Consequently $V$ starts with zero slope, and after a shoulder of length of order $1/\max(c, d_I)$ it decays exponentially at the rate $\min(c, d_I)$ of the longer-lived population. The decay curve depends only on the two lifespans $1/c$ and $1/d_I$, not on $\lambda$, $\beta$, $k$ or the pre-treatment $R_0$.

## Depends on

- [Basic viral dynamics model and its within-host basic reproductive number](basic-viral-dynamics-model-and-its-reproductive-number.md)

## Proof depends on

- [Uniqueness of the first-order solution](../../../../Chemistry/chemical-kinetics/rate-laws/first-order-sol-unique.md)
- [Duhamel's formula (variation of constants)](../../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md)

## Proof sketch

With $\beta = 0$ the $I$ equation decouples, $\dot I = -d_I I$, and $\dot V = k I(0) e^{-d_I t} - c V$ is a linear equation whose solution with $V(0) = V_0$ and $k I(0) = c V_0$ is the formula above; it satisfies $V(0) = V_0$ and $\dot V(0) = 0$. For HIV, free virus lives about an hour ($c$ of order $25$ per day) while the observed first-phase decay under combination therapy has a slope of about one per day, so $c \gg d_I$ and the decay rate measures the death rate of virus-producing cells, $d_I \approx 1$ per day. That short lifespan implies a large daily turnover of newly infected cells at setpoint. When therapy is imperfect but still brings the treated reproductive number below one, the decay slope is nearly insensitive to the exact efficacy, so viral load decay curves reveal infected-cell lifespans but say little about drug potency. Later, slower phases of decay are attributed to longer-lived infected cell populations and to the latent reservoir.

## Sources

- A. L. Hill, D. I. S. Rosenbloom, M. A. Nowak and R. F. Siliciano, "Insight into treatment of HIV infection from viral dynamics models", Immunological Reviews 285 (2018), Section 2.1 (Equation 3, Figures 2–3), <https://doi.org/10.1111/imr.12698>, PMCID: PMC6155466.
