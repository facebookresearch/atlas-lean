# Age-structured PDE limit of the multi-patch epidemic with migration and varying infectivity

**Model.** A population of size $N$ is distributed over patches $\ell \in \{1,\ldots,L\}$. Susceptible, infected and recovered individuals migrate from patch $\ell$ to $\ell'$ at rates $\nu^S_{\ell,\ell'}$, $\nu^I_{\ell,\ell'}$, $\nu^R_{\ell,\ell'}$; let $Q$ be the generator of the infected migration chain and $p_{\ell',\ell}(t) = (e^{Qt})_{\ell'\ell}$. Each infected individual has an i.i.d. random infectivity function of its infection age with mean $\bar\lambda(\mathfrak a)$ and an infectious period with distribution function $F$ (density $f$, hazard $\mu = f/F^c$). A susceptible in patch $\ell$ is infected at rate $\beta_{\ell,\ell'} / B^N_\ell(t)^{\gamma}$ times the total current infectivity in patch $\ell'$, summed over $\ell'$, with $\gamma \in [0,1]$ and $B_\ell$ the patch population. Let $\mathfrak I^N_\ell(t,\mathfrak a)$ count infected individuals in patch $\ell$ with infection age at most $\mathfrak a$, and use bars for division by $N$.

**Theorem (functional law of large numbers).** Under convergence of the initial conditions and bounded infectivity, $(\bar S^N_\ell, \bar{\mathfrak I}^N_\ell, \bar R^N_\ell)_\ell$ converges in probability, locally uniformly in $t$ and $\mathfrak a$, to the unique continuous solution of a system of Volterra-type integral equations in which new infections in patch $\ell'$ at time $s$ contribute total infectivity $\bar\lambda(t-s)p_{\ell',\ell}(t-s)$ in patch $\ell$ at time $t$.

**Theorem (PDE representation).** If $\bar{\mathfrak I}_\ell(0,\cdot)$ and $F$ have densities, then $\bar{\mathfrak I}_\ell(t,\cdot)$ has a density $\bar{\mathfrak i}_\ell(t,\mathfrak a)$, and the row vector $\bar{\mathfrak i} = (\bar{\mathfrak i}_\ell)_\ell$ is the unique solution of

$$\partial_t \bar{\mathfrak i}(t,\mathfrak a) + \partial_{\mathfrak a}\bar{\mathfrak i}(t,\mathfrak a) = -\mu(\mathfrak a)\,\bar{\mathfrak i}(t,\mathfrak a) + \bar{\mathfrak i}(t,\mathfrak a)\,Q,$$

with boundary condition

$$\bar{\mathfrak i}_\ell(t,0) = \frac{\bar S_\ell(t)}{\bar B_\ell(t)^\gamma}\sum_{\ell'}\beta_{\ell,\ell'}\int_0^\infty \bar\lambda(\mathfrak a)\,\bar{\mathfrak i}_{\ell'}(t,\mathfrak a)\,\frac{F^c((\mathfrak a-t)^+)}{F^c(\mathfrak a)}\,d\mathfrak a .$$

Explicitly, $\bar{\mathfrak i}(t,\mathfrak a) = \frac{F^c(\mathfrak a)}{F^c(\mathfrak a-t)}\bar{\mathfrak i}(0,\mathfrak a - t)e^{Qt}$ for $t \le \mathfrak a$ and $\bar{\mathfrak i}(t,\mathfrak a) = F^c(\mathfrak a)\,\bar{\mathfrak i}(t-\mathfrak a,0)\,e^{Q\mathfrak a}$ for $t > \mathfrak a$, where the incidence $\bar{\mathfrak i}(\cdot,0)$ solves a closed system of integral equations together with $\bar S_\ell$, $\bar I_\ell$, $\bar R_\ell$.

## Depends on

- [Kermack–McKendrick final-size relation](../kermack-mckendrick-sir-model/final-size.md)

## Expansion

The individual-based process is written with Poisson random measures: each infection event creates an individual whose infectivity curve, infectious period and migration path are independent. Averaging over these independent marks, the total infectivity in patch $\ell$ at time $t$ from individuals infected in patch $\ell'$ at time $s$ concentrates on $\bar\lambda(t-s)p_{\ell',\ell}(t-s)$; tightness in the space $D(\mathbb{R}_+, D(\mathbb{R}_+))$ of age-indexed processes and uniqueness of the integral equations give the law of large numbers. Along characteristics $t - \mathfrak a = $ const, individuals age at unit speed, are removed at hazard $\mu(\mathfrak a)$ and migrate according to $Q$, which is the transport PDE; the factor $F^c((\mathfrak a - t)^+)/F^c(\mathfrak a)$ accounts for initially infected individuals whose infectivity is conditioned on their age at time $0$.

## Sources

- Guodong Pang, Etienne Pardoux, "PDE model for multi-patch epidemic models with migration and infection-age dependent infectivity", arXiv:2304.03080 (2023), Theorems 2.1 and 3.1, <https://doi.org/10.48550/arXiv.2304.03080>.
