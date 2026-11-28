# Effect of variability in cell aging rates on the Malthus parameter

**Model.** Cells carry a physiological age $a\ge0$ and an individual aging rate $v\in\mathcal V$, a compact subset of $(0,\infty)$. The density $n(t,a,v)$ solves the age-structured equation with variability

$$\partial_tn+\partial_a\big(v\,n\big)+vB(a)\,n=0,\qquad v'\,n(t,0,v')=2\rho(v')\iint vB(a)\,n(t,a,v)\,dv\,da,$$

so age advances at speed $v$ and division occurs at rate $vB(a)$, where $B:[0,a_{\max})\to[0,\infty)$ is continuous with $\int^{a_{\max}}B=\infty$. Each daughter draws its rate independently from a continuous, bounded density $\rho$ on $\mathcal V$ with mean $\bar v$ (no heredity). Write $\Psi_B(a)=B(a)\exp(-\int_0^aB)$ for the division-age density at unit speed.

**Malthus parameter.** The dominant eigenvalue $\lambda_{B,\rho}>0$ of this model (the growth rate in $n\approx e^{\lambda t}N$) exists, is unique with positive direct and adjoint eigenvectors, and is the unique root of

$$2\iint e^{-\lambda_{B,\rho}a/v}\,\Psi_B(a)\,\rho(v)\,dv\,da=1 .$$

The reference population, in which every cell ages at $\bar v$, has $\lambda_{B,\bar v}$ solving $2\int_0^\infty e^{-\lambda_{B,\bar v}a/\bar v}\Psi_B(a)\,da=1$.

**Theorem (sign of the effect).** Assume $B$ is differentiable.
1. For $a_{\max}\in(0,\infty]$: if $B'(a)<B(a)^2$ on $[0,a_{\max})$, then $\lambda_{B,\rho}<\lambda_{B,\bar v}$; variability slows growth.
2. For $a_{\max}<\infty$: if $\Psi_B$ is bounded and $B'(a)>B(a)^2$ on $[0,a_{\max})$, then $\lambda_{B,\rho}>\lambda_{B,\bar v}$.

**Theorem (small variability).** For the mean-preserving family $\rho_\alpha(v)=\alpha^{-1}\rho\big(\alpha^{-1}(v-(1-\alpha)\bar v)\big)$, $\alpha\in(0,1]$, with variance $\alpha^2\sigma^2$, $\sigma^2=\int(v-\bar v)^2\rho$, the map $\alpha\mapsto\lambda_{B,\rho_\alpha}$ is twice differentiable and

$$\lambda_{B,\rho_\alpha}=\lambda_{B,\bar v}+\frac{\alpha^2}{2}\,\frac{d^2\lambda_{B,\rho_\alpha}}{d\alpha^2}\Big|_{\alpha=0}+o(\alpha^2),$$

$$\frac{d^2\lambda_{B,\rho_\alpha}}{d\alpha^2}\Big|_{\alpha=0}=\sigma^2\Big(\int_0^\infty\frac{a}{\bar v}e^{-\lambda_{B,\bar v}a/\bar v}\Psi_B(a)\,da\Big)^{-1}\int_0^\infty\frac{\lambda_{B,\bar v}a}{\bar v}\Big(\frac{\lambda_{B,\bar v}a}{\bar v}-2\Big)e^{-\lambda_{B,\bar v}a/\bar v}\Psi_B(a)\,da .$$

## Expansion

The characteristic equation follows by integrating the stationary eigenproblem along characteristics: a cell of rate $v$ divides at age $a$ with density $\Psi_B(a)$, reached after time $a/v$, so the renewal condition is the Euler–Lotka equation averaged over $\rho$. Comparing the two characteristic equations reduces to the convexity in $v$ of $v\mapsto\int e^{-\lambda a/v}\Psi_B(a)\,da$; integrating by parts, its second derivative has the sign of $B'-B^2$, and Jensen's inequality gives the comparison. The second-order formula is implicit differentiation of the characteristic equation; the first derivative vanishes at $\alpha=0$ because the mean is fixed. For constant $B$ (exponential division times, $B'=0<B^2$) variability always lowers the Malthus parameter; simulations of the size-structured analogue show a decrease of about 2% for coefficients of variation of 15–20%.

## Sources

- Adélaïde Olivier, "How does variability in cell aging and growth rates influence the Malthus parameter?", Kinetic & Related Models 10 (2017), 481–512, <https://doi.org/10.3934/krm.2017019>. Published version of arXiv:1602.06970, cited next; locators there refer to the arXiv version.
- Adélaïde Olivier, "How does variability in cells aging and growth rates influence the Malthus parameter?", arXiv:1602.06970 (2016): Model (A+V), Theorem 4 (eigenproblem), Theorem 5 (comparison), Theorem 6 with Lemma 8 and Propositions 9–10 (perturbation). <https://doi.org/10.48550/arXiv.1602.06970>
