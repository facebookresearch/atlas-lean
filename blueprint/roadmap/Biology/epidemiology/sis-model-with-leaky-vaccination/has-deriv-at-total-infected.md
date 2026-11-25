# The total-infected equation

Let $N \ne 0$ and $\gamma \ne 0$, and let $(S_u, I_u, S_v, I_v)$ be a [solution](is-solution.md) of
the SIS model with leaky vaccination, with transmission rate $\beta$, recovery rate $\gamma$,
vaccine efficacy $\varepsilon$ and population size $N$, with group sizes
$S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$ for some real $p$. Then at every $t \ge 0$
the total infected $I = I_u + I_v$ has derivative

$$
I'(t) = \gamma (R_v - 1) I(t) -
\frac{\beta}{N} I(t) \bigl(I_u(t) + (1 - \varepsilon) I_v(t)\bigr),
$$

with the [vaccinated reproduction number](rv.md) $R_v = (\beta / \gamma)(1 - \varepsilon p)$.
