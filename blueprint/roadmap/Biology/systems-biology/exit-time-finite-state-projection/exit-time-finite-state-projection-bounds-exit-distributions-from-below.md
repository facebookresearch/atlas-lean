# Exit time finite state projection bounds exit distributions from below

**Setting.** $X$ is a minimal time-homogeneous continuous-time Markov chain on a countable state space $\mathcal{S}$ (e.g. molecule counts of a stochastic reaction network) with stable, conservative rate matrix $Q = (q(x,y))$, explosion time $T_\infty$ and initial law $\gamma$. For a domain $\mathcal{D} \subseteq \mathcal{S}$ let $\tau = \inf\{t < T_\infty : X_t \notin \mathcal{D}\}$ be the exit time. The *exit distribution* $\mu(dt, x)$ is the joint law of $(\tau, X_\tau)$ on $\{\tau < \infty\}$ and the *occupation measure* is $\nu(dt, x) = \mathbb{P}(X_t = x,\ t < \tau)\,dt$ on $\mathcal{D}$. Assume $\sum_{x \in \mathcal{D}} \gamma(x)|q(x,x)| < \infty$. Then $\mu$ and $\nu$ have continuous densities given by $\nu(t,x) = \mathbf{1}_{\mathcal{D}}(x)\hat p_t(x)$ and $\mu(t,x) = \mathbf{1}_{\mathcal{D}^c}(x)\dot{\hat p}_t(x)$, where $\hat p$ is the minimal nonnegative solution of $\dot{\hat p}_t(x) = \sum_{y \in \mathcal{D}} \hat p_t(y) q(y,x)$, $\hat p_0 = \gamma$ (the forward equation of the chain stopped on leaving $\mathcal{D}$).

**ETFSP scheme.** Choose an increasing sequence of finite truncations $\mathcal{S}_r \subseteq \mathcal{S}$ and final times $t^r_f$, put $\mathcal{D}_r = \mathcal{D} \cap \mathcal{S}_r$, and solve the finite linear system

$$
\dot\nu^r(t,x) = \sum_{y \in \mathcal{D}_r} \nu^r(t,y)\, q(y,x), \quad \nu^r(0,x) = \gamma(x) \ \ (x \in \mathcal{D}_r), \qquad \mu^r(t,x) = \sum_{y \in \mathcal{D}_r} \nu^r(t,y)\, q(y,x) \ \ (x \in \mathcal{S}_r \cap \mathcal{D}^c)
$$

on $[0, t^r_f]$ (with an atom $\gamma(x)$ at $t = 0$ for initial states outside $\mathcal{D}$).

**Theorem.** Let $\tau_r$ be the exit time from $\mathcal{S}_r$ and $\|\cdot\|$ the total variation norm.

1. *(Lower bounds.)* $\mu^0 \le \mu^1 \le \dots \le \mu$ and $\nu^0 \le \nu^1 \le \dots \le \nu$ pointwise.
2. *(Masses.)* $\mu^r([0,\infty), \mathcal{S}) = \mathbb{P}(\tau \le t^r_f \wedge \tau_r)$ and $\nu^r([0,\infty), \mathcal{S}) = \mathbb{E}\big[(\tau \wedge t^r_f)\mathbf{1}_{\{\tau \le \tau_r\}}\big]$.
3. *(Computable error bounds.)* $\|\mu - \mu^r\| = \mathbb{P}(\tau < \infty) - \mathbb{P}(\tau \le t^r_f \wedge \tau_r) \le \varepsilon_r := 1 - \gamma(\mathcal{D}^c \cap \mathcal{S}_r) - \sum_{x \in \mathcal{D}^c \cap \mathcal{S}_r} \int_0^{t^r_f} \mu^r(t,x)\,dt$, with equality iff the chain leaves $\mathcal{D}$ almost surely; and $\|\nu - \nu^r\| = \mathbb{E}[\tau \wedge T_\infty] - \mathbb{E}[(\tau \wedge t^r_f)\mathbf{1}_{\{\tau \le \tau_r\}}] \le \mathbb{E}[\tau] - \sum_{x \in \mathcal{D}_r} \int_0^{t^r_f} \nu^r(t,x)\,dt$.
4. *(Monotonicity and convergence.)* The errors and their bounds decrease as $r$ grows, and if $\bigcup_r \mathcal{S}_r = \mathcal{S}$ and $t^r_f \to \infty$ the errors tend to $0$; the same holds for the time and space marginals of $\mu$ and $\nu$.

For the classical finite state projection (FSP) of the time-$t$ law $p_t$, the analogous statements are: $p^r_t$ increases to $p_t$, has mass $\mathbb{P}(t < \tau_r)$, and $\|p_t - p^r_t\| = \mathbb{P}(t < T_\infty) - \mathbb{P}(t < \tau_r) \le 1 - p^r_t(\mathcal{S}_r)$ with equality iff the chain is non-explosive.

## Expansion

The truncated system is the forward equation of the chain killed when it leaves $\mathcal{D}_r$, so $\nu^r(t,x) = \mathbb{P}(X_t = x,\ t < \tau \wedge \tau_r)$ and $\mu^r(t,x)$ is the density of exits from $\mathcal{D}$ into $x$ before leaving $\mathcal{S}_r$; enlarging $\mathcal{S}_r$ only adds paths, which gives monotone lower bounds and the mass formulas. A pathwise coupling (via the Gillespie construction) with a chain whose rates agree on $\mathcal{D}$ shows that only the rates inside $\mathcal{D}$ matter. Applications include first-passage times of gene expression and fixation times of competing species, where $\varepsilon_r$ certifies the accuracy without simulation.

## Sources

- J. Kuntz, P. Thomas, G.-B. Stan, M. Barahona, "The exit time finite state projection scheme: bounding exit distributions and occupation measures of continuous-time Markov chains", arXiv:1801.09507 (2018): Section 1 (ETFSP scheme and its main theorem), Section 2 (preliminaries: forward equations, FSP theorem, analytical characterisation of $\mu$ and $\nu$), Section 3 (proof of the main theorem and the corollary on marginals), Section 4 (applications). <https://doi.org/10.48550/arXiv.1801.09507>
