# Exit time finite state projection bounds exit distributions from below

**Setting.** $X$ is a minimal time-homogeneous continuous-time Markov chain on a countable state space $\mathcal{S}$ (e.g. molecule counts of a stochastic reaction network) with stable, conservative rate matrix $Q = (q(x,y))$, explosion time $T_\infty$ and initial law $\gamma$. For a domain $\mathcal{D} \subseteq \mathcal{S}$ let $\tau = \inf\{t < T_\infty : X_t \notin \mathcal{D}\}$ be the exit time ($\inf\emptyset=\infty$). The *exit distribution* $\mu(dt, x)$ is the joint law of $(\tau, X_\tau)$ on $\{\tau < \infty\}$ and the *occupation measure* is $\nu(dt, x) = \mathbb{P}(X_t = x,\ t < \tau\wedge T_\infty)\,dt$. Assume $\sum_{x \in \mathcal{D}} \gamma(x)|q(x,x)| < \infty$. Then $\nu(dt,x)=\nu(t,x)\,dt$ with $\nu(t,x) = \mathbf{1}_{\mathcal{D}}(x)\hat p_t(x)$, and the exit distribution splits into an atom at time $0$ and a part with a continuous density on $[0,\infty)$,

$$
\mu(dt,x)=\mathbf{1}_{\mathcal{D}^c}(x)\,\gamma(x)\,\delta_0(dt)+\mu(t,x)\,dt,\qquad \mu(t,x) = \mathbf{1}_{\mathcal{D}^c}(x)\,\dot{\hat p}_t(x),
$$

where $\hat p$ is the minimal nonnegative solution of $\dot{\hat p}_t(x) = \sum_{y \in \mathcal{D}} \hat p_t(y) q(y,x)$, $\hat p_0 = \gamma$ (the forward equation of the chain stopped on leaving $\mathcal{D}$). The atom is the mass of the chains started outside $\mathcal{D}$, which exit at $\tau=0$; when $\gamma$ is supported in $\mathcal{D}$ it vanishes and $\mu$ has a continuous density on $[0,\infty)$.

**ETFSP scheme.** Choose nested finite truncations $\mathcal{S}_0\subseteq\mathcal{S}_1\subseteq\dots\subseteq\mathcal{S}$ and nondecreasing final times $t^0_f\le t^1_f\le\dots$ in $[0,\infty)$, put $\mathcal{D}_r = \mathcal{D} \cap \mathcal{S}_r$, and solve the finite linear system

$$
\dot\nu^r(t,x) = \sum_{y \in \mathcal{D}_r} \nu^r(t,y)\, q(y,x), \quad \nu^r(0,x) = \gamma(x) \ \ (x \in \mathcal{D}_r), \qquad \mu^r(t,x) = \sum_{y \in \mathcal{D}_r} \nu^r(t,y)\, q(y,x) \ \ (x \in \mathcal{S}_r \cap \mathcal{D}^c)
$$

on $[0, t^r_f]$, extended by $0$ elsewhere. The approximating measures are $\nu^r(dt,x)=\nu^r(t,x)\,dt$ and $\mu^r(dt,x)=\mathbf{1}_{\mathcal{D}^c\cap\mathcal{S}_r}(x)\,\gamma(x)\,\delta_0(dt)+\mu^r(t,x)\,dt$.

**Theorem.** Let $\tau_r = \inf\{t<T_\infty : X_t\notin\mathcal{S}_r\}$ be the exit time from $\mathcal{S}_r$ and $\|\cdot\|$ the total variation norm.

1. *(Lower bounds.)* $\mu^0(t,x) \le \mu^1(t,x) \le \dots \le \mu(t,x)$ and $\nu^0(t,x) \le \nu^1(t,x) \le \dots \le \nu(t,x)$ for all $x\in\mathcal{S}$ and $t\ge0$.
2. *(Masses.)* $\nu^r(t,x)=\mathbb{P}(X_t=x,\ t<\tau\wedge\tau_r)$ for $t\le t^r_f$, so $\nu^r([0,\infty), \mathcal{S}) = \mathbb{E}[\tau\wedge\tau_r\wedge t^r_f]$; and $\mu^r$ counts exactly the exits from $\mathcal{D}$ into a state of $\mathcal{S}_r$ made while the chain has stayed in $\mathcal{S}_r$, so $\mu^r([0,\infty), \mathcal{S}) = \mathbb{P}(\tau \le t^r_f,\ \tau<\tau_r)$.
3. *(Computable error bounds.)* $\|\mu - \mu^r\| = \mathbb{P}(\tau < \infty) - \mathbb{P}(\tau \le t^r_f,\ \tau<\tau_r) \le \varepsilon_r := 1 - \gamma(\mathcal{D}^c \cap \mathcal{S}_r) - \sum_{x \in \mathcal{D}^c \cap \mathcal{S}_r} \int_0^{t^r_f} \mu^r(t,x)\,dt$, with equality if and only if the chain leaves $\mathcal{D}$ almost surely. If $\mathbb{E}[\tau\wedge T_\infty]<\infty$, then $\|\nu - \nu^r\| = \mathbb{E}[\tau \wedge T_\infty] - \mathbb{E}[\tau\wedge\tau_r\wedge t^r_f] \le \mathbb{E}[\tau] - \sum_{x \in \mathcal{D}_r} \int_0^{t^r_f} \nu^r(t,x)\,dt$.
4. *(Monotonicity.)* $\|\mu-\mu^r\|$ and $\varepsilon_r$ are nonincreasing in $r$, and so are $\|\nu-\nu^r\|$ and its bound when $\mathbb{E}[\tau\wedge T_\infty]<\infty$.
5. *(Convergence.)* If $\bigcup_r \mathcal{S}_r = \mathcal{S}$ and $t^r_f \to \infty$, then $\|\mu-\mu^r\|\to0$, the same holds for the time and space marginals of $\mu$, and $\varepsilon_r\to0$ if and only if $\mathbb{P}(\tau<\infty)=1$. If in addition $\mathbb{E}[\tau\wedge T_\infty]<\infty$, then $\|\nu-\nu^r\|\to0$, and likewise for the marginals of $\nu$. Without this integrability $\nu$ can have infinite mass (a chain that stays forever in one state of $\mathcal{D}$), and no finite cutoff approximates it in total variation.

For the classical finite state projection (FSP) of the time-$t$ law $p_t$, the analogous statements are: $p^r_t$ increases to $p_t$, has mass $\mathbb{P}(t < \tau_r)$, and $\|p_t - p^r_t\| = \mathbb{P}(t < T_\infty) - \mathbb{P}(t < \tau_r) \le 1 - p^r_t(\mathcal{S}_r)$ with equality iff the chain is non-explosive.

## Expansion

The truncated system is the forward equation of the chain killed when it leaves $\mathcal{D}_r$, so $\nu^r(t,x) = \mathbb{P}(X_t = x,\ t < \tau \wedge \tau_r)$ for $x\in\mathcal{D}_r$, and integrating over $[0,t^r_f]$ gives the mass of $\nu^r$. A jump from $\mathcal{D}_r$ to a state of $\mathcal{S}_r\cap\mathcal{D}^c$ is an exit from $\mathcal{D}$ strictly before the exit from $\mathcal{S}_r$; a jump from $\mathcal{D}_r$ to a state outside $\mathcal{S}_r$ kills the truncated chain and is not counted, even when it also leaves $\mathcal{D}$ (then $\tau=\tau_r$). This gives the mass of $\mu^r$. Enlarging $\mathcal{S}_r$ and $t^r_f$ only adds paths, which gives monotone lower bounds. A pathwise coupling (via the Gillespie construction) with a chain whose rates agree on $\mathcal{D}$ shows that only the rates inside $\mathcal{D}$ matter. Applications include first-passage times of gene expression and fixation times of competing species, where $\varepsilon_r$ certifies the accuracy without simulation.

## Sources

- J. Kuntz, P. Thomas, G.-B. Stan, M. Barahona, "The exit time finite state projection scheme: bounding exit distributions and occupation measures of continuous-time Markov chains", SIAM Journal on Scientific Computing 41 (2019) A748–A769, <https://doi.org/10.1137/18M1168261>, preprint arXiv:1801.09507: Section 1 (ETFSP scheme and its main theorem), Section 2 (preliminaries: forward equations, FSP theorem, analytical characterisation of $\mu$ and $\nu$), Section 3 (proof of the main theorem and the corollary on marginals), Section 4 (applications). The mass and error identities above count exits strictly before $\tau_r$ and use $\tau\wedge\tau_r\wedge t^r_f$ for the occupation mass, where the printed Theorem 1.1(ii)–(iii) uses the indicator of $\tau\le\tau_r$.
