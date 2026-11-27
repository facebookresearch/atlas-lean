# Immune-status-structured cholera model linking within-host and between-host dynamics

**Within-host model.** Target cells $T$, the *Vibrio cholerae* load $P$ and the immune response $W$ satisfy

$$ \dot T = \Lambda - \mu T - \alpha P^2T, \qquad \dot P = \alpha P^2T - \gamma P - \delta PW, \qquad \dot W = \varepsilon(\kappa P - cW), $$

where the quadratic incidence $\alpha P^2T$ models an Allee effect (quorum sensing), and $\varepsilon \ll 1$ makes the immune response slow. Solutions with nonnegative data stay nonnegative, and $\Omega = \{T + P \le \frac{\Lambda}{\mu+\gamma} + 1,\ W \le \frac{\kappa\Lambda}{c(\mu+\gamma)} + 1\}$ is absorbing. In the fast system ($\varepsilon \to 0$, $W$ frozen, $\Gamma = \gamma + \delta W$):
- the infection-free state $E_0 = (\Lambda/\mu, 0)$ is always locally asymptotically stable;
- for $\Lambda > 2\Gamma\sqrt{\mu/\alpha}$ there are also infected states $E_1 = (T^*,P^*)$ with $T^* = \Lambda/(\mu + \alpha P^{*2})$ and $P^* = \frac{1}{2\Gamma\alpha}\big[\alpha\Lambda \pm \sqrt{\alpha^2\Lambda^2 - 4\alpha\mu\Gamma^2}\big]$, born in a saddle-node bifurcation;
- a Hopf point occurs when $\mu = \Gamma - \Gamma^4/(\alpha\Lambda^2)$ with $\Gamma > 2\mu$. (The source's Proposition 3 states $\Gamma > \mu$, which is automatic from the equation; at the trace-zero point the Jacobian has determinant $\Gamma(\Gamma - 2\mu)$, so $\Gamma > 2\mu$ is needed for purely imaginary eigenvalues.)

As the slow immune variable $W$ grows, $\Gamma$ crosses the saddle-node threshold and the infected branch disappears. In the singular limit $\varepsilon \to 0$ the pathogen is then eliminated in finite time (for $\varepsilon > 0$, $P(t)$ stays positive), unlike in within-host models where it only decays asymptotically.

**Between-host model.** Infected hosts are structured by immune status $\omega \in [0,\omega_0]$, which increases at rate $g(\omega)$ derived from the within-host immune response; the pathogen load $P(\omega)$ sets infectivity and shedding. With susceptibles $S$, infected density $I(t,\omega)$, immune hosts $V$ (losing immunity at rate $\rho$) and environmental bacteria $B$:

$$
\begin{aligned}
\dot S &= r - \mu_1S - S\int_0^{\omega_0}\beta_hP(\omega)I(t,\omega)\,d\omega - \beta_eSB + \rho V,\\
\partial_tI + \partial_\omega\big(g(\omega)I\big) &= -\mu_2(\omega)I, \qquad g(0)I(t,0) = S\int_0^{\omega_0}\beta_hPI\,d\omega + \beta_eSB,\\
\dot V &= g(\omega_0)I(t,\omega_0) - (\rho + \mu_3)V, \qquad \dot B = \int_0^{\omega_0}\xi(\omega)P(\omega)I(t,\omega)\,d\omega - \sigma B .
\end{aligned}
$$

**Theorem.** The disease-free equilibrium $(r/\mu_1,0,0,0)$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$, where, with survival factor $\pi(\omega) = \exp\big(-\int_0^\omega\mu_2/g\big)$,

$$ \mathcal{R}_0 = \frac{r\beta_h}{\mu_1}\int_0^{\omega_0}\frac{P(\omega)}{g(\omega)}\pi(\omega)\,d\omega + \frac{r\beta_e}{\mu_1}\int_0^{\omega_0}\frac{\xi(\omega)}{\sigma}\frac{P(\omega)}{g(\omega)}\pi(\omega)\,d\omega $$

(the direct and environmental routes). The endemic equilibrium exists for $\mathcal{R}_0 > 1$, and is locally stable under additional parameter constraints.

**Variant with a maximal bacterial age.** Let environmental bacteria carry an age $a \in [0,\bar a]$, $\bar a < \infty$, with $(\partial_t + \partial_a)B(t,a) = -\sigma B(t,a)$, $B(t,0) = \int_0^{\omega_0}\xi(\omega)P(\omega)I(t,\omega)\,d\omega$ and $B(t) = \int_0^{\bar a}B(t,a)\,da$ in the force of infection. Its basic reproduction number $\bar{\mathcal R}_0$ is $\mathcal R_0$ with the factor $1/\sigma$ in the environmental term replaced by $(1 - e^{-\sigma\bar a})/\sigma$ (the mean environmental lifetime of a bacterium truncated at age $\bar a$). Without loss of immunity ($\rho = 0$), the endemic equilibrium of this variant is globally asymptotically stable whenever $\bar{\mathcal R}_0 > 1$. The source proves global stability only for this variant, not for the model above.

## Expansion

Along characteristics $d\omega/dt = g(\omega)$, an infected host spends time $d\omega/g(\omega)$ at immune status $\omega$ and survives with probability $\pi(\omega)$. During that time it infects at rate $\beta_hP(\omega)S_0$ directly, and sheds $\xi(\omega)P(\omega)$ bacteria, each of which lives $1/\sigma$ on average and infects at rate $\beta_eS_0$. Integrating over $\omega$ gives the two terms of $\mathcal{R}_0$. Local stability follows from the characteristic equation of the linearized age-structured system. Global stability for $\rho = 0$ uses a Volterra-type Lyapunov functional for the maximal-age variant, in which both routes become integrals with compactly supported kernels over past forces of infection.

## Sources

- Beryl Musundi, "An Immuno-epidemiological Model Linking Between-host and Within-host Dynamics of Cholera", arXiv:2105.12675 (2021), Section 2 (within-host model, positivity, absorbing set, time-scale analysis, fast-system equilibria and Hopf point), Section 3 (between-host model, explicit solution along characteristics, $\mathcal{R}_0$ and stability of the disease-free and endemic equilibria), <https://doi.org/10.48550/arXiv.2105.12675>.
