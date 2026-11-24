# Initial Picard increment with constant drift and diffusion

Let $B$ have real Brownian finite-dimensional laws, be adapted to $(\mathcal F_t)$, and have increments independent of the past filtration. Fix real constants $a,c$. Let $J$ be a martingale with continuous paths for every sample and with fixed-time almost-sure equality to the actual Itô integral of the constant integrand $a$, at every nonnegative time. For every $t\ge0$,

$$\mathbb E\sup_{0\le s\le t}|J_s+cs|^2
\le(8|a|^2+2t|c|^2)t.$$

The expectation is the nonnegative extended integral. The factor eight comes from the two-term square bound and Doob's factor four; the drift contributes $2c^2t^2$. These are sufficient, nonoptimal constants. Setting $a=\sigma(x)$ and $c=b(x)$ controls the first increment of Picard iteration from the constant process $x$. Zero time and zero coefficients are included. No filtration completeness, right continuity or continuous integrator paths are required.
