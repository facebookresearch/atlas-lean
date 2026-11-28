# Endemic threshold of a reinfection model with waning immunity and recurrent vaccination

**Model.** In a closed population, each individual alternates between an infectious state $I$ and a (partially) susceptible state $S$. On infection it draws a random infectiousness curve $\lambda : [0, T_I) \to [0,\infty)$ (with random infectious period $T_I$); on recovery, and again at each vaccination, it draws an independent random non-decreasing susceptibility curve $\sigma : [0,\infty) \to [0,1]$, describing waning immunity as a function of the time since the last immunizing event. Susceptible individuals are re-vaccinated according to a renewal process with i.i.d. inter-dose times distributed as $T_V$, until reinfected. A susceptible individual of age $a$ (time since last immunization) is infected at rate $\sigma(a)\Lambda(t)$, where $\Lambda(t)$ is the population-average infectiousness. The basic reproduction number is

$$
R_0 = \int_0^\infty \mathbb{E}[\lambda(a)]\,da < \infty .
$$

As the population size $N \to \infty$, the age-structured densities $I(t,a)$, $S(t,a)$ of infectious and susceptible individuals converge to the unique weak solution of a McKean–Vlasov/transport PDE system.

**Statement.** Let $\mu_I$ and $\mu_V$ be the hazard rates of $T_I$ and $T_V$.

1. *Disease-free equilibrium.* The limiting PDE has a unique disease-free equilibrium, $S(a) = \mathbb{E}[T_V]^{-1}\exp\bigl(-\int_0^a \mu_V(u)\,du\bigr)$, the stationary age law of the vaccination renewal process.
2. *Endemic equilibria.* Endemic equilibria correspond one-to-one to positive solutions $x$ of $F_e(x) = R_0$, where

$$
F_e(x) = x\,\mathbb{E}[T_I] + x\,\frac{\mathbb{E}\Bigl[\int_0^{T_V} e^{-x\int_0^a \sigma(u)\,du}\,da\Bigr]}{\mathbb{E}\Bigl[1 - e^{-x\int_0^{T_V}\sigma(u)\,du}\Bigr]},
$$

with $x = R_0 I(0)$ the equilibrium force of infection, $I(a) = I(0)e^{-\int_0^a \mu_I}$ and $S(a) = S(0)e^{-\int_0^a\mu_V}\,\mathbb{E}\bigl[e^{-x\int_0^a\sigma}\bigr]$.
3. *Threshold.* Define the mean susceptibility at the disease-free equilibrium

$$
\Sigma = \frac{\mathbb{E}\bigl[\int_0^{T_V}\sigma(a)\,da\bigr]}{\mathbb{E}[T_V]} = \lim_{x \downarrow 0} \frac{1}{F_e(x)} .
$$

An endemic equilibrium exists whenever $R_0\Sigma > 1$. If $\sigma$ is deterministic, or of SIRS type $\sigma(a) = \mathbf 1_{\{a \ge T_R\}}$ with $\mathbb{E}[T_R] < \infty$, then $F_e$ is increasing and there is a unique endemic equilibrium if and only if $R_0\Sigma > 1$, and none otherwise.
4. *Optimal dose timing.* Write $\Phi(t) = \int_0^t \mathbb{E}[\sigma(a)]\,da$, a convex function, so $\Sigma = \mathbb{E}[\Phi(T_V)]/\mathbb{E}[T_V]$. Among vaccination policies using the same number of doses per unit time, $\mathbb{E}[T_V] = m$, Jensen's inequality gives $\Sigma \ge \Phi(m)/m$, with equality for evenly spaced doses $T_V \equiv m$. More generally, if $T_1 \preceq T_2$ in the convex order (same mean, less dispersed), then $\Sigma_1 \le \Sigma_2$; and scaling $T_V \mapsto mT_V$ makes $\Sigma$ increasing in $m$.

Thus recurrent vaccination prevents endemicity exactly when it lowers the stationary mean susceptibility below $1/R_0$, and regular schedules are the most dose-efficient way to do so.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Stationary solutions satisfy $I' = -\mu_I I$ and $S' = -\mu_V S - \mathbb{E}_a[\sigma(a)]\Lambda S$, giving the stated profiles, and $\Lambda = I(0)R_0$. The boundary condition $I(0) = \Lambda\int_0^\infty \mathbb{E}_a[\sigma(a)]S(a)\,da$ yields $S(0) = I(0)/\mathbb{E}[1 - e^{-x\int_0^{T_V}\sigma}]$, and normalizing $\int I + \int S = 1$ is exactly $F_e(x) = R_0$. Writing $\phi(a) = \int_0^a\sigma$, $F_e(x) = x\,\mathbb{E}[T_I] + \mathbb{E}[\int_0^{T_V}e^{-x\phi}]/\mathbb{E}[\int_0^{T_V}\sigma e^{-x\phi}]$. In the SIRS case this equals $x\,\mathbb{E}[T_I] + 1 + \mathbb{E}[T_V \wedge T_R]/\mathbb{E}[\int_0^{(T_V - T_R)_+}e^{-xa}da]$, visibly increasing. In the deterministic case the derivative's numerator is a symmetrized double integral of $(\sigma(a)-\sigma(b))(\phi(a)-\phi(b))e^{-x(\phi(a)+\phi(b))} \ge 0$, since $\sigma$ and $\phi$ are both non-decreasing. The threshold has a branching interpretation: an infective in the disease-free population makes on average $R_0$ contacts, each hitting an individual whose susceptibility has mean $\Sigma$, so the initial branching process is supercritical iff $R_0\Sigma > 1$.

## Sources

- Félix Foutel-Rodier, Arthur Charpentier and Hélène Guérin, "Optimal vaccination policy to prevent endemicity: a stochastic model", *Journal of Mathematical Biology* 90 (2025), 10, <https://doi.org/10.1007/s00285-024-02171-z>. Preprint version: arXiv:2306.13633 (2023), Section 2 (model and Eq. for $R_0$), Section 3, Propositions 3 and 4, and Section 4.2 (optimal strategy for a fixed cost), <https://doi.org/10.48550/arXiv.2306.13633>.
