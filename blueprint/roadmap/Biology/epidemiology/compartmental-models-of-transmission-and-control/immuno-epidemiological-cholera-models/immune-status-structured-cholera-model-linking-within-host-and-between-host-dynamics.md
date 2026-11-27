# Immune-status-structured cholera model linking within-host and between-host dynamics

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

## Expansion

Along characteristics $d\omega/dt = g(\omega)$, an infected host spends time $d\omega/g(\omega)$ at immune status $\omega$ and survives with probability $\pi(\omega)$. During that time it infects at rate $\beta_hP(\omega)S_0$ directly, and sheds $\xi(\omega)P(\omega)$ bacteria, each of which lives $1/\sigma$ on average and infects at rate $\beta_eS_0$. Integrating over $\omega$ gives the two terms of $\mathcal{R}_0$. Local stability follows from the characteristic equation of the linearized age-structured system.

## Sources

- Beryl Musundi, "An immuno-epidemiological model linking between-host and within-host dynamics of cholera", Math. Biosci. Eng. 20(9) (2023), Section 3 (between-host model, $\mathcal{R}_0$, Theorems 3.2–3.3 and Proposition 3.3); preprint arXiv:2105.12675 (2021), <https://doi.org/10.48550/arXiv.2105.12675>.
