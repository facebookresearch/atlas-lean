# Fleming-Viot approximation of the Yaglom limit of Bellman-Harris processes

**Setting.** In a Bellman-Harris process with parameters $(G,h)$ each individual lives an independent lifetime with law $G$ (continuous density $g$, hazard rate $\mu=g/(1-G)$) and at death is replaced by an independent number $\xi$ of newborns with generating function $h(s)=\sum_n p_ns^n$ and mean $m=h'(1)$. Ages make the population size non-Markov, so one follows the age configuration $\eta_t=\sum_{i\text{ alive}}\delta_{a_i(t)}$, a strong Markov process on finite point measures on $\mathbb R_+$ in which ages grow at unit speed and an individual of age $a$ is replaced at rate $\mu(a)$ via $\eta\mapsto\eta-\delta_a+\xi\delta_0$. Let $\tau$ be the extinction time and $E$ the set of nonzero configurations. In the subcritical regime (the paper's hypotheses (H1)-(H6) on bounded hazards, offspring moments and a Lyapunov function $V$), extinction happens from a single individual of age $a$ at rate $\kappa(\eta)=p_0\,\mu(a)$ when $\eta=\delta_a$. A *quasi-stationary distribution* (QSD) $\nu$ on $E$ satisfies $\mathbb P_\nu(\eta_t\in\cdot\mid\tau>t)=\nu$; the *Yaglom limit* is $\nu_Y=\lim_t\mathbb P_{\delta_0}(\eta_t\in\cdot\mid\tau>t)$. The **Fleming-Viot particle system** runs $N\ge2$ independent copies of $\eta$ in $E$; when a copy would go extinct, it instead jumps to the current configuration of another copy chosen uniformly. Its empirical measure at stationarity is $\mathcal X^N$.

**Theorem 3.6 (consistency).** For every $N\ge2$ the particle system is exponentially ergodic with a unique invariant law; $\sup_{N\ge2}\mathbb E[\mathcal X^N(V)]<\infty$; and every deterministic subsequential limit $\nu^*$ of $\mathcal X^N$ is quasi-stationary with decay rate $\nu^*(\kappa)$.

**Theorem 3.7 (selection of the Yaglom limit).** Under (H1)-(H6):
1. the killed process has a unique QSD $\nu_{\mathrm{QSD}}$ with $\nu_{\mathrm{QSD}}(V)<\infty$, and there are $c,\gamma>0$ with $\|\mathbb P_{\pi_0}(\eta_t\in\cdot\mid\tau>t)-\nu_{\mathrm{QSD}}\|_{\mathrm{TV}}\le c\,\pi_0(V)e^{-\gamma t}$ for every initial law with $\pi_0(V)<\infty$;
2. $\nu_{\mathrm{QSD}}=\nu_Y$, with decay rate the Malthusian parameter $\lambda_0$;
3. there is $d>0$ independent of $N$ such that for every bounded measurable $\varphi$ and every $N\ge2$,

$$\mathbb E\bigl|\mathcal X^N(\varphi)-\nu_Y(\varphi)\bigr|\le\frac{d}{N^{\varpi}}\|\varphi\|_\infty,\qquad \varpi=\frac{\gamma}{2(\|\kappa\|_\infty+\gamma)}\in\bigl(0,\tfrac12\bigr).$$

**Corollary 3.8.** The Malthusian parameter is the mean killing rate under the Yaglom limit: $\lambda_0=\nu_Y(\kappa)=p_0\int_0^\infty\mu(a)\,\nu_Y^{(1)}(da)$, where $\nu_Y^{(1)}$ is the restriction of $\nu_Y$ to single-individual configurations $\{\delta_a:a\ge0\}$, viewed as a measure on ages.

## Expansion

Uniform exponential convergence of the conditioned laws comes from a Lyapunov-plus-small-set criterion on configuration space: because lifetimes are not exponential, the Galton-Watson Lyapunov functions in the population size fail and must be replaced by functionals of the ages, and the mass $Z_t$ is only a supermartingale for the original process, not for the particle system. Given this, a general theorem for Fleming-Viot systems with bounded killing rate turns the exponential rate $\gamma$ and the killing bound $\|\kappa\|_\infty$ into the polynomial rate $N^{-\varpi}$, with a moment bound uniform in $N\ge2$ removing the usual lower restriction on $N$. Applied to calibrated outbreak data, the empirical measure serves as a stationary estimator of the conditioned state of a subcritical epidemic, used for change detection in livestock disease surveillance.

## Sources

- O. Arezki, P.-M. Grollemund, A. Zemouche, "Fleming-Viot selection of the Yaglom limit for age-structured Bellman-Harris processes, with application to livestock epidemic surveillance", arXiv preprint (2026), Theorem 3.6, Theorem 3.7, Corollary 3.8, <https://doi.org/10.48550/arXiv.2607.29251>.
