# Link between the subdistribution hazard and the cumulative incidence

Let $T$ be a failure time and $J$ a failure cause on a probability space, $F_c(t) = P(T \le t, J = c)$ the cumulative incidence of cause $c$ and $F_c(t-) = P(T < t, J = c)$. If $t \ge 0$, $F_c$ is continuous on $[0, t]$, differentiable on $(0, t)$ with interval-integrable derivative, and $F_c(t) < 1$, then $1 - F_c(t) = (1 - F_c(0))\exp(-\Lambda^*_c(t))$, where $\Lambda^*_c(t) = \int_0^t\lambda^*_c$ is the integral of the subdistribution hazard.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
