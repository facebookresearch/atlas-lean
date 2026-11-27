# Extinction and persistence in a stochastic SICA model with Lévy jumps

**Model.** The SICA model of HIV/AIDS tracks susceptibles $S$, HIV-infected individuals without AIDS symptoms $I$, chronically infected individuals on antiretroviral treatment $C$, and AIDS patients $A$. Transmission is perturbed by white noise of intensity $\sigma$ and by Lévy jumps with intensity $J(u)$:

$$\begin{aligned}
dS&=(\Lambda-\beta IS-\mu S)\,dt-\sigma IS\,dW_t-\int_UJ(u)I(t^-)S(t^-)\,\tilde N(dt,du),\\
dI&=\big(\beta IS-(\rho+\phi+\mu)I+\alpha A+\omega C\big)dt+\sigma IS\,dW_t+\int_UJ(u)I(t^-)S(t^-)\,\tilde N(dt,du),\\
dC&=\big(\phi I-(\omega+\mu)C\big)dt,\\
dA&=\big(\rho I-(\alpha+\mu+d)A\big)dt,
\end{aligned}$$

where $\tilde N$ is a compensated Poisson random measure with finite intensity $\nu$ on $U$. Here $\phi$ is the rate of starting treatment, $\omega$ the rate of treatment failure back to $I$, $\rho$ the rate of progression to AIDS, $\alpha$ the rate of AIDS patients returning to $I$ under treatment, and $d$ the AIDS-induced death rate.

**Theorem.**

1. For initial data in the biologically feasible region $\Omega$, there is almost surely a unique global positive solution. Moreover $\limsup_{t\to\infty}S(t)\le\Lambda/\mu$ and $\liminf_{t\to\infty}S(t)\ge\Lambda/(\mu+d)$ almost surely, with analogous bounds for the other compartments.
2. *(Extinction.)* If $\dfrac{\beta^2}{2\sigma^2}<(\rho+\phi+\mu)+(\alpha+\omega)\dfrac{\Lambda}{\mu}$, then $I(t)\to0$ almost surely.
3. *(Persistence in the mean.)* If $\beta\dfrac{\Lambda}{\mu+d}>(\rho+\phi+\mu)+\dfrac{\sigma^2\Lambda^2}{2\mu^2}$, then

$$\liminf_{t\to\infty}\frac1t\int_0^tI(s)\,ds\ \ge\ \frac1{\rho+\phi+\mu}\Big(\frac{\beta\Lambda}{\mu+d}-(\rho+\phi+\mu)-\frac{\sigma^2\Lambda^2}{2\mu^2}\Big)>0 .$$

## Proof sketch

Positivity and global existence follow from a Lyapunov function of logarithmic type and a stopping-time argument. The finite jump measure keeps the jump terms integrable. For extinction, Itô's formula for $\log I$ gives a drift $\beta S-(\rho+\phi+\mu)+\dots-\tfrac12\sigma^2S^2$. Maximizing the quadratic in $S$ bounds it by $\beta^2/(2\sigma^2)$. The strong law for the martingale terms then forces $\log I(t)/t$ to be negative. For persistence, integrating the $I$ equation and using the lower bound on $S$ shows that the time-averaged infection stays positive. Large noise can therefore eradicate the infection even when the deterministic reproduction number exceeds one, while moderate noise only lowers the persistence level.

## Sources

- Houssine Zine, Jaouad Danane and Delfim F.M. Torres, "Stochastic SICA epidemic model with jump Lévy processes", in *Mathematical Analysis of Infectious Diseases*, Elsevier, 2022, 61–72, <https://doi.org/10.1016/b978-0-32-390504-6.00009-7>. Preprint version: arXiv:2202.00546 (2022), Section 1 (model), Theorem 2.1 (global positive solution and bounds), Theorem 3.1 (extinction), Theorem 4.1 (persistence in the mean), <https://doi.org/10.48550/arXiv.2202.00546>.
