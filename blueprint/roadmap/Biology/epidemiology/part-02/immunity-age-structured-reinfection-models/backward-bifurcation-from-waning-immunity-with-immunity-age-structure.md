# Backward bifurcation from waning immunity with immunity-age structure

Susceptibles $S$, latents $E$, asymptomatic $A$ and symptomatic $I$ infectives, and immune individuals with density $r(t,\tau)$ over **immunity age** $\tau$ (time since vaccination or recovery) evolve as

$$S' = \Lambda - \beta_s S\,\frac{\theta E + \epsilon A + I}{N} - (\alpha + u)S, \qquad E' = \Big(\beta_s S + \int_0^\infty \beta_r(\tau)\,r(t,\tau)\,d\tau\Big)\frac{\theta E + \epsilon A + I}{N} - (\sigma + u)E,$$

$$A' = (1-\rho)\sigma E - (\gamma_A + u)A, \qquad I' = \rho\sigma E - (\gamma_I + \mu + u)I,$$

$$\partial_t r + \partial_\tau r = -\beta_r(\tau)\frac{\theta E + \epsilon A + I}{N}\,r - u r, \qquad r(t,0) = \alpha S + \gamma_A A + \gamma_I I,$$

with $N = S + E + A + I + \int_0^\infty r\,d\tau$, recruitment $\Lambda$, vaccination rate $\alpha$, natural and disease death $u, \mu$, relative infectiousness $\theta, \epsilon$ of latents and asymptomatics, symptomatic fraction $\rho$, and a reinfection susceptibility $\beta_r(\tau) = \bar\beta\,\beta_{r0}(\tau)$ that grows as immunity declines, $\beta_{r0} \in (0,1]$. The disease-free equilibrium is $P_0 = (\Lambda/(\alpha+u), 0, 0, 0, \tfrac{\alpha\Lambda}{\alpha+u}e^{-u\tau})$ and

$$\mathcal R_0 = \frac{1}{(\sigma+u)N^0}\Big(\beta_s S^0 + \int_0^\infty \beta_r(\tau) r^0(\tau)\,d\tau\Big)\Big(\theta + \frac{(1-\rho)\sigma\epsilon}{\gamma_A + u} + \frac{\rho\sigma}{\gamma_I + \mu + u}\Big),$$

$N^0 = S^0 + \int_0^\infty r^0$. Let $\bar\beta^*$ be the value of $\bar\beta$ with $\mathcal R_0 = 1$, write $K = \theta + \frac{(1-\rho)\sigma\epsilon}{\gamma_A + u} + \frac{\rho\sigma}{\gamma_I + \mu + u}$ and $J = \int_0^\infty \beta_{r0}(\tau)e^{-u\tau}\,d\tau$, and define the quadratic-nonlinearity coefficient

$$a = \frac{2u}{\Lambda}K\Big[\bar\beta^* J\Big(\frac{\alpha(\sigma+u)}{\alpha+u} + \frac{\gamma_A(1-\rho)\sigma}{\gamma_A + u} + \frac{\gamma_I\rho\sigma}{\gamma_I + \mu + u}\Big) - \frac{u}{\alpha+u}\big(\beta_s + \alpha\bar\beta^* J\big)\Big(1 + \frac{(1-\rho)\sigma}{u} + \frac{(\gamma_I + u)\rho\sigma}{u(\gamma_I + \mu + u)}\Big) - \frac{\alpha u}{\alpha+u}(\bar\beta^*)^2 K\int_0^\infty \beta_{r0}(\tau)e^{-u\tau}\!\int_0^\tau \beta_{r0}(h)\,dh\,d\tau\Big].$$

(The source's eq. (3) prints the third term in the second bracket as $\frac{(\gamma_I + u)\rho\sigma}{\gamma_I + \mu + u}$, a rate added to dimensionless terms; the kernel vector gives $\hat x_4(1 + \gamma_I/u) = \frac{(\gamma_I + u)\rho\sigma}{u(\gamma_I + \mu + u)}$, as written here.)

**Theorem.** At $\mathcal R_0 = 1$ the disease-free equilibrium undergoes a transcritical bifurcation, which is **backward** if $a > 0$ and **forward** if $a < 0$.

In the backward case a stable endemic equilibrium coexists with the stable disease-free state for $\mathcal R_0$ in an interval $(\mathcal R_0^{\mathrm{fsn}}, 1)$ ending at a saddle-node, so lowering $\mathcal R_0$ just below $1$ does not eliminate the disease from large initial outbreaks; numerically, even the forward branch can fold back through two saddle-nodes, producing bistability of two endemic states above $1$.

## Expansion

Linearizing at $P_0$ gives a simple zero eigenvalue at $\bar\beta = \bar\beta^*$ (i.e. $\mathcal R_0 = 1$) with explicit right and left null vectors. A Lyapunov–Schmidt reduction of the infinite-dimensional steady-state problem onto this kernel yields a scalar bifurcation equation whose quadratic coefficient is proportional to $a$; its sign decides whether endemic equilibria emerge for $\mathcal R_0 < 1$ (backward) or $\mathcal R_0 > 1$ (forward). The first term in the bracket comes from reinfection of immune individuals and is the only positive contribution, so a backward bifurcation requires sufficiently strong reinfection relative to primary transmission $\beta_s$.

## Sources

- Shuanglin Jing, Ling Xue, Jichen Yang, "Backward bifurcation arising from decline of immunity against emerging infectious diseases", arXiv (2024). Model (COVID_BB_EQ1) with boundary condition, disease-free equilibrium and $\mathcal R_0$, coefficient $a$ (EQ_DI4), Theorem 1.1, numerical section on saddle-node branches. <https://doi.org/10.48550/arXiv.2406.01957>. Published version: Applied Mathematics Letters 158 (2024), article 109241, <https://doi.org/10.1016/j.aml.2024.109241>; locators above refer to the arXiv version.
