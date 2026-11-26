# Lyapunov gap at non-smooth fold bifurcations of a forced Allee model

Consider the time-forced Allee population model

$$
x'(t) = \frac{r}{K^2}\,x(t)\,(K - x(t))\,(x(t) - S) - \big(\beta + \kappa F(t)\big)\,x(t),
$$

with growth rate $r > 0$, carrying capacity $K$, Allee threshold $0 < S < K$, harvesting/mortality parameter $\beta$ and forcing amplitude $\kappa \ge 0$, where the forcing is either quasiperiodic, $F(t) = \prod_{i=1}^d \big(\tfrac{1+\sin(2\pi(\theta_i + t\nu_i))}{2}\big)^q$, or bounded random, $F(t) = \tfrac{1 + \sin(\theta_0 + W_t)}{2}$ with $W$ a Brownian motion. Put $b = \frac{r}{K^2}\big(\frac{K-S}{2}\big)^2$, $\gamma = \frac19\big(\frac{K+S}{K-S}\big)^2$, assume $\kappa < b(1-\gamma)$, and let $J = [b(1-\gamma), b+1]$. For $\beta < \beta_c$ let $x^s_\beta$ and $x^u_\beta$ be the stable and unstable non-autonomous equilibria (invariant graphs) that collide in a fold bifurcation at $\beta_c \in J$, and $\lambda(\cdot)$ their Lyapunov exponents.

**Theorem.** If the fold bifurcation at $\beta_c$ is non-smooth, then

$$
\lim_{\beta \nearrow \beta_c} \lambda(x^s_\beta) = \lambda(x^s_{\beta_c}) < 0 ,
$$

and analogously the exponent of $x^u_\beta$ stays bounded away from $0$. If the fold bifurcation is smooth, then $\lim_{\beta\nearrow\beta_c} \lambda(x^s_\beta) = 0$. The same dichotomy holds for general parameter families of forced monotone $C^2$ flows with concave fibre maps satisfying the saddle-node framework of Anagnostopoulou and Jäger.

## Expansion

In a smooth fold the two invariant graphs merge continuously and the stable exponent tends to $0$: recovery from perturbations slows down, the classical early-warning signal. In a non-smooth fold, which occurs for an open set of quasiperiodically forced families with Diophantine frequencies, the graphs touch only on a dense set of fibres while remaining apart elsewhere; the exponent is the average of $\partial_x V$ along the graph and stays strictly negative up to the bifurcation. Hence asymptotic recovery rates give no warning of the imminent collapse to extinction in forced populations.

## Sources

- Flavia Remo, Gabriel Fuhrmann and Tobias Jäger, *On the effect of forcing of fold bifurcations and early-warning signals in population dynamics*, arXiv:1904.06507, Theorem 1 (Section 1) and Theorem 4.1 (Section 4). <https://doi.org/10.48550/arXiv.1904.06507> Published version: Nonlinearity 35 (2022) 6485–6527, <https://doi.org/10.1088/1361-6544/ac98ee>.
