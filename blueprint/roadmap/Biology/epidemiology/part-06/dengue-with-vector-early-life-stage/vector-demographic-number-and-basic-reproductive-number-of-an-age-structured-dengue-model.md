# Vector demographic number and basic reproductive number of an age-structured dengue model

**Model.** Mosquitoes pass through an early-life (egg/larva) stage $E(t)$ and are susceptible $S_v$ or infected $I_v$, with $N_v = S_v + I_v$. Eggs are laid at the Kolmogorov-type rate $f(N_v) = N_v\, g(N_v)$, where $g \ge 0$ is differentiable, $g(0) > 0$ and $g(\infty) = 0$; eggs die at rate $\mu_e$ and mature at rate $\delta$; adults die at rate $\mu_v$. Hosts are structured by age $a$ with mortality $\mu_h(a)$, age-specific vector-to-host transmission $\beta(a)$ and recovery $\gamma(a)$; with host proportions $s_h, i_h, r_h$ of the age density $n(t,a)$,

$$\frac{dE}{dt} = f(N_v) - (\delta + \mu_e)E, \qquad \frac{dS_v}{dt} = \delta E - \beta_v B(t) S_v - \mu_v S_v, \qquad \frac{dI_v}{dt} = \beta_v B(t) S_v - \mu_v I_v,$$

$$(\partial_t + \partial_a) s_h = -\beta(a) s_h \frac{I_v}{N_v}, \qquad (\partial_t + \partial_a) i_h = \beta(a) s_h \frac{I_v}{N_v} - \gamma(a) i_h, \qquad (\partial_t + \partial_a) r_h = \gamma(a) i_h,$$

where $B(t) = \int_0^\infty p(t,a)\, i_h(t,a)\, da$ is the force of infection on vectors under proportional mixing, $p(t,a) = c(a) n(t,a)/\int_0^\infty c\, n\, da$ with activity rate $c(a)$, and $p_\infty(a)$ is its limit at the stationary host age distribution $n^*(a) = \Lambda e^{-\int_0^a \mu_h}$. Set

$$\phi = \frac{(\delta + \mu_e)\mu_v}{\delta}.$$

**Vector demography.** Positive vector states are the solutions of $g(N_v^*) = \phi$, each giving $(E^*, N_v^*) = (\mu_v N_v^*/\delta, N_v^*)$. Such a state is locally asymptotically stable if the vector demographic number

$$\mathcal{R}_v = \frac{f'(N_v^*)}{\phi} = 1 + g'(N_v^*)\frac{N_v^*}{\phi}$$

satisfies $\mathcal{R}_v < 1$ (i.e. $g'(N_v^*) < 0$), and unstable otherwise. The vector-free state is locally asymptotically stable if $g(0) < \phi$ and unstable otherwise. Several vector states can coexist when $g$ is non-monotone.

**Theorem.** Define

$$\mathcal{R}_0 = \frac{\beta_v}{\mu_v}\int_0^\infty\!\!\int_0^a p_\infty(a)\, \beta(\tau)\, e^{-\int_\tau^a \gamma(h)\,dh}\, d\tau\, da,$$

which for constant parameters reduces to $\mathcal{R}_0 = \beta_v\beta/\big(\mu_v(\mu_h + \gamma)\big)$. If $\mathcal{R}_0 < 1$, the disease-free solution is globally asymptotically stable. If some vector state $N^*$ with $g(N^*) = \phi$ and $g'(N^*) < 0$ exists and $\mathcal{R}_0 > 1$, there is an endemic, age-nonuniform stable steady state.

## Expansion

Linearizing the vector equations at $(E^*, N_v^*)$ with perturbations $e^{\psi t}$ gives a characteristic equation $\mathcal{H}_v(\psi) = 1$ with $\mathcal{H}_v$ decreasing on $[0,\infty)$ and $\mathcal{H}_v(0) = \mathcal{R}_v$, so no root has nonnegative real part exactly when $\mathcal{R}_v < 1$. For the infection, $\mathcal{R}_0 = G(0)$, where $G(\psi) = 1$ is the characteristic equation of the infected subsystem: a host infected at age $\tau$ stays infectious to age $a$ with probability $e^{-\int_\tau^a \gamma}$, contributes to vector infection with weight $p_\infty(a)$, and an infected vector lives $1/\mu_v$ on average. The vector demographic threshold and the epidemiological threshold thus separate.

## Sources

- F. Sanchez and J. G. Calvo, "Dengue model with early-life stage of vectors and age-structure within host", arXiv:1908.02434 (2019), Section 2 (model), Section 3.1 (Lemmas 3.1 and 3.3, vector demographic number), Section 3.2 (basic reproductive number, Theorems 3.4 and 3.5), <https://doi.org/10.48550/arXiv.1908.02434>.
