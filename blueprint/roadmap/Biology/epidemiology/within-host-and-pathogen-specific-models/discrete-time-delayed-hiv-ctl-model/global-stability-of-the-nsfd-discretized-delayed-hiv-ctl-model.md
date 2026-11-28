# Global stability of the NSFD-discretized delayed HIV model with CTL response

**Continuous model.** Let $X, Y, V, Z$ be uninfected CD4$^+$ cells, infected cells, free virus and cytotoxic T lymphocytes, with intracellular delay $\tau \ge 0$:

$$\dot X = \lambda - dX - \beta XV,\quad \dot Y = \beta X(t-\tau)V(t-\tau) - aY - pYZ,\quad \dot V = aNY - \mu V,\quad \dot Z = cXYZ - sZ,$$

all parameters positive ($N$ is the burst size). Define

$$\mathcal R_0 = \frac{\beta N\lambda}{d\mu}, \qquad \mathcal R_1 = \frac{\beta N(\lambda c\mu - \beta s a N)}{d c\mu^2} = \mathcal R_0\,\frac{\lambda c\mu - \beta s aN}{\lambda c\mu} < \mathcal R_0 .$$

The equilibria are the infection-free point $E_0 = (\lambda/d, 0,0,0)$, the immune-free infected point $E^* = \big(\tfrac{\mu}{\beta N}, \tfrac{\beta N\lambda - d\mu}{\beta N a}, \tfrac{\beta N\lambda - d\mu}{\beta\mu}, 0\big)$ (positive iff $\mathcal R_0 > 1$), and the CTL-active point $\overline E$ with $\overline X = \tfrac{\lambda c\mu - \beta saN}{dc\mu}$ (positive iff $\mathcal R_1 > 1$).

**Discrete model.** With step $\phi > 0$, $\tau = m\phi$ for an integer $m$, and Mickens' nonstandard finite-difference (NSFD) scheme

$$\begin{aligned}
\tfrac{X_{n+1}-X_n}{\phi} &= \lambda - dX_{n+1} - \beta X_{n+1}V_n, &
\tfrac{Y_{n+1}-Y_n}{\phi} &= \beta X_{n-m+1}V_{n-m} - aY_{n+1} - pY_{n+1}Z_n,\\
\tfrac{V_{n+1}-V_n}{\phi} &= aNY_{n+1} - \mu V_{n+1}, &
\tfrac{Z_{n+1}-Z_n}{\phi} &= cX_nY_{n+1}Z_n - sZ_{n+1},
\end{aligned}$$

with nonnegative initial values on $\{-m, \dots, 0\}$ and positive values at $0$, every solution is positive and ultimately bounded, and the equilibria coincide with those of the continuous model.

**Theorem.** For every step size $\phi > 0$:
1. if $\mathcal R_0 \le 1$, $E_0$ is globally asymptotically stable;
2. if $\mathcal R_1 \le 1 < \mathcal R_0$, $E^*$ is globally asymptotically stable;
3. if $\mathcal R_1 > 1$, $\overline E$ is globally asymptotically stable.

## Proof sketch

Because each update is linear in the new value, the scheme can be solved explicitly (for instance $X_{n+1} = (\lambda\phi + X_n)/(1 + d\phi + \beta\phi V_n)$), which gives positivity for all $\phi$. Global stability uses discrete Volterra-type Lyapunov functions built from $g(x) = x - 1 - \ln x \ge 0$, evaluated at the equilibrium in question and augmented by finite sums over the delay window $n-m, \dots, n$, whose increments are shown to be nonpositive; the inequality $Y^* < \overline Y$ when $\mathcal R_1 < 1 < \mathcal R_0$ is used to separate cases 2 and 3. The result shows the NSFD discretization is dynamically consistent: it reproduces the threshold structure of the continuous delay model without step-size restrictions.

## Sources

- Sandra Vaz and Delfim F. M. Torres, "Discrete-Time System of an Intracellular Delayed HIV Model with CTL Immune Response", in *Springer Proceedings in Mathematics & Statistics*, Springer International Publishing, 2022, 211–229, <https://doi.org/10.1007/978-3-031-17558-9_12>. Preprint version: arXiv:2205.02199 (2022), Section 3 (NSFD model, Lemma 1, Theorems 4–6, Lemma 2), <https://doi.org/10.48550/arXiv.2205.02199>.
