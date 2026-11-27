# Herd immunity threshold under gamma-distributed susceptibility or connectivity

**Model.** Individuals carry a trait $x \ge 0$ with initial density $q(x)$, $\int x q = 1$, $\int (x - 1)^2 q = \nu^2$. With compartments $S(x,t), E(x,t), I(x,t), R(x,t)$ (total population $1$),

$$\partial_t S(x) = -\lambda x S(x), \quad \partial_t E(x) = \lambda x S(x) - \delta E(x), \quad \partial_t I(x) = \delta E(x) - \gamma I(x), \quad \partial_t R(x) = \gamma I(x),$$

where $x$ is *susceptibility* with force of infection $\lambda = \beta \int I(x)\,dx$, or *connectivity* with $\lambda = \beta \int x I(x)\,dx$. Write $S = \int S(x)$, $\bar S = \int x S(x)$, $\bar{\bar S} = \int x^2 S(x)$. Then $R_0 = \beta/\gamma$ and $R_{\mathrm{eff}} = R_0 \bar S$ for susceptibility, while $R_0 = (1 + \nu^2)\beta/\gamma$ and $R_{\mathrm{eff}} = (\beta/\gamma)\bar{\bar S}$ for connectivity. A configuration with no infection is at the herd immunity threshold when $R_{\mathrm{eff}} = 1$.

**Gamma case.** If $q$ is a gamma density with mean $1$ and coefficient of variation $\nu > 0$, and the epidemic is seeded with vanishing initial infection, then along the epidemic

$$\bar S = S^{1 + \nu^2}, \qquad \bar{\bar S} = (1 + \nu^2)\, S^{1 + 2\nu^2},$$

so the susceptibility model closes exactly as $\dot S = -\beta I S^{1 + \nu^2}$, $\dot E = \beta I S^{1+\nu^2} - \delta E$, $\dot I = \delta E - \gamma I$, $\dot R = \gamma I$, and the proportion ever infected when the threshold is reached is

$$H_{\mathrm{susc}} = 1 - R_0^{-1/(1 + \nu^2)}, \qquad H_{\mathrm{conn}} = 1 - R_0^{-1/(1 + 2\nu^2)},$$

both below the homogeneous value $1 - 1/R_0$ for $R_0 > 1$ and decreasing in $\nu$.

## Expansion

Integrating $\partial_t S(x) = -\lambda x S(x)$ gives $S(x, t) = q(x) e^{-x\Lambda(t)}$ with $\Lambda = \int_0^t \lambda$ (vanishing seed). For a gamma law of shape $k = 1/\nu^2$ and rate $k$, $\int q(x) x^m e^{-x\Lambda}dx = \frac{\Gamma(k + m)}{\Gamma(k) k^m}(1 + \Lambda/k)^{-k-m}$, giving $S = (1 + \nu^2\Lambda)^{-1/\nu^2}$, $\bar S = (1 + \nu^2\Lambda)^{-1/\nu^2 - 1} = S^{1+\nu^2}$ and $\bar{\bar S} = (1+\nu^2)(1 + \nu^2\Lambda)^{-1/\nu^2 - 2} = (1+\nu^2) S^{1 + 2\nu^2}$. Setting $R_{\mathrm{eff}} = 1$ gives $S^{1+\nu^2} = 1/R_0$, respectively $S^{1+2\nu^2} = 1/R_0$, and $H = 1 - S$.

## Depends on

- [The SEIR vector field on ℝ⁴](seir-field.md)

## Sources

- A. Montalbán, R. M. Corder and M. G. M. Gomes, "Herd immunity under individual variation and reinfection", *Journal of Mathematical Biology* (2022), <https://doi.org/10.1007/s00285-022-01771-x> (PMC9246817). Equations (1)–(12), Sections 2–4 and Appendix A.
