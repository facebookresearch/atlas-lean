# Latent mean differences are not identified without invariance constraints

Consider two groups $g = 1, 2$ and one observed indicator $X = \nu_g + \lambda_g F + \varepsilon$ with $F \sim N(\kappa_g, \phi_g)$ and independent $\varepsilon \sim N(0, \psi)$, all parameters group-specific. Parameterization A: $\nu_1 = \nu_2 = 0$, $\lambda_1 = \lambda_2 = 1$, $\phi_1 = \phi_2 = \psi = 1$, $\kappa_1 = 0$, $\kappa_2 = 1$. Parameterization B: the same, except $\nu_2 = 2$ and $\kappa_2 = -1$. Both give $X \sim N(0, 2)$ in group $1$ and $X \sim N(1, 2)$ in group $2$, yet the latent mean difference $\kappa_2 - \kappa_1$ is $+1$ in A and $-1$ in B. More generally, replacing $F$ in group $g$ by $a_g + b_gF$ with $b_g \ne 0$ and compensating $\nu_g$, $\lambda_g$, $\kappa_g$, $\phi_g$ preserves every group's observed law. So latent means cannot be compared across groups without cross-group constraints on the measurement parameters; which constraints suffice is a separate question.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
