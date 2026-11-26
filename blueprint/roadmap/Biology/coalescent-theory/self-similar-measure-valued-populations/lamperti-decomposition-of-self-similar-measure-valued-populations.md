# Lamperti decomposition of self-similar measure-valued populations

**Definitions.** A Markov process $(X_t)$ in a cone of a normed space (e.g. finite measures $\mathcal M(E)$ on a compact Polish type space $E$, with $\|\mu\|=\mu(E)$) is *$\alpha$-self-similar* ($\alpha$-SS) if $\mathcal L(X_t\mid X_0=x)=\mathcal L(aX_{a^{-\alpha}t}\mid X_0=a^{-1}x)$ for all $a>0$. A *Markov additive process* (MAP) $(\rho_t,\xi_t)$ on $S\times\mathbb R$ is a Markov process whose increments of $\xi$ depend on the past only through the current $\rho_t$.

**Theorem (Lamperti transformation in normed spaces).** Let $X$ be a standard $\alpha$-SS Markov process and $c_\alpha(t)=\inf\{s:\int_0^s\|X_u\|^{-\alpha}du\ge t\}$. Then
$$(\rho_t,\xi_t)=\Big(\frac{X_{c_\alpha(t)}}{\|X_{c_\alpha(t)}\|},\ \log\|X_{c_\alpha(t)}\|\Big)$$
is a standard MAP, and conversely every MAP yields an $\alpha$-SS process $e^{\xi}\rho$ after the inverse time change $\gamma_\alpha$; this is a bijection.

**Theorem (self-similar populations).** For $\sigma\ge0$, $b\in\mathbb R$, a finite measure $\Lambda$ on $(0,1)$ and $\alpha\ge0$, there is a measure-valued $\alpha$-SS Markov process $(\mu_t)$ with generator
$$\mathcal F_\alpha F(\mu)=\|\mu\|^{-\alpha}\big(\mathcal G_bF+\mathcal G_\sigma F+\mathcal G_\Lambda F\big)(\mu),$$
$$\mathcal G_bF(\mu)=b\!\int\!\mu(da)F'(\mu;a),\qquad \mathcal G_\sigma F(\mu)=\|\mu\|\!\int\!\mu(da)\tfrac{\sigma^2}2F''(\mu;a,a),$$
$$\mathcal G_\Lambda F(\mu)=\int\frac{\mu(da)}{\|\mu\|}\int_{(0,1)}\frac{\Lambda(d\zeta)}{\zeta^2}\Big\{F\Big(\mu+\|\mu\|\tfrac{\zeta}{1-\zeta}\delta_a\Big)-F(\mu)-\|\mu\|\,|\log(1-\zeta)|\mathbf 1_{\zeta<1/2}F'(\mu;a)\Big\},$$
in which an individual of type $a$ (chosen from $\mu/\|\mu\|$) produces a block of offspring of mass proportional to the **total** population size. After the time change $c_\alpha$, the type-frequency process $\mu/\|\mu\|$ is a $(\Lambda+\sigma^2\delta_0)$-Fleming–Viot process and $\log\|\mu\|$ is a Lévy process with triplet $(b-\sigma,\sigma,\Pi)$, $\Pi$ the image of $\zeta^{-2}\Lambda(d\zeta)$ under $\zeta\mapsto-\log(1-\zeta)$; the total size $\|\mu_t\|$ is a positive self-similar Markov process. The genealogy is described by a dual pair $(\Pi_t,Z_t)$ with $\Pi_t$ a $(\Lambda+\sigma^2\delta_0)$-coalescent and $\log Z_t$ a Lévy process.

## Depends on

- [Infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process](../coalescents/infinite-lookdown-de-finetti-limit-and-lambda-fl.md)
- [The genealogy of α-stable branching is a time-changed Beta-coalescent](../partition-valued-kingman-coalescent/alpha-stable-csbp-genealogy-is-a-time-changed-be.md)

## Expansion

The Feller diffusion (Dawson–Watanabe) superprocess is $1$-SS, and after the Lamperti time change its normalized state is a Fleming–Viot process while its log-mass is Brownian motion with drift, recovering the classical result that the genealogy of a continuous-state branching population is a time-changed coalescent. The jump term is chosen so that a jump $\nu\to\nu+\|\nu\|x\,\delta_a$ with $x=\zeta/(1-\zeta)$ changes frequencies by $\rho\to\rho/(1+x)+\tfrac{x}{1+x}\delta_a=(1-\zeta)\rho+\zeta\delta_a$, exactly the reproduction event of a $\Lambda$-Fleming–Viot process. Because offspring sizes scale with total size, these populations are not branching processes, yet self-similarity plays the role of the branching property: the factor $\|\mu\|^{-\alpha}$ regulates the reproduction rate by population size, and choosing $\alpha$ and $\Lambda$ suitably embeds known results such as the Beta-coalescent genealogy of $\alpha$-stable branching.

## Sources

- A. Siri-Jégousse, A. Hernández Wences, "The Lamperti transformation in the infinite-dimensional setting, self-similar populations, and coalescents", arXiv:2405.10193 (2024), Section 1 (definitions of self-similarity and MAPs, main result for measure-valued populations), Section 2 (Lamperti transformation in normed spaces), Section 3.3 (Dawson–Watanabe process) and Section 4 (construction, duality and Lamperti transformation theorems), <https://doi.org/10.48550/arXiv.2405.10193>.
