# Small-noise phase diffusion along a stable limit cycle

**Setting.** Let $F: \mathbb{R}^d \to \mathbb{R}^d$ be $C^2$ and suppose $\dot x = F(x)$ has a hyperbolic, locally stable limit cycle $M = \{q_t : t \in [0,T)\}$ of period $T$ with basin $W$. Every $y \in W$ lies on a unique isochron $W(q_t)$ (the stable fibre of $q_t$, a smooth $(d-1)$-dimensional hypersurface transverse to $F$); its *asymptotic phase* $\theta(y) \in \mathbb{R}/T\mathbb{Z}$ is that $t$, and the deterministic flow moves $\theta$ at unit speed. Add small noise:

$$dX^\varepsilon_t = F(X^\varepsilon_t)\,dt + \varepsilon\,G(X^\varepsilon_t)\,dB_t,$$

with $G$ locally Lipschitz, $d \times m$-matrix valued, and $B$ an $m$-dimensional Brownian motion. Let $\tau_{\varepsilon,W}$ be the exit time from $W$, $x_t$ the noiseless trajectory from $x_0$, and $\tilde\theta^\varepsilon_t$ the continuous lift of $\theta\big(X^\varepsilon_{\cdot\wedge\tau_{\varepsilon,W}}\big)$ evaluated at time $\varepsilon^{-2}t$.

**Theorem.** Assume $X_0^\varepsilon \to x_0 \in W$ in probability and fix $t_f > 0$.
1. *Proximity and phase limit on the time scale $\varepsilon^{-2}$.* For every $s_\varepsilon = o(\varepsilon^{-2})$ there is $\eta_\varepsilon = o(1)$, and for every $\beta \in (0,1)$ there is $c_\beta > 0$, such that with probability tending to $1$,

$$\sup_{s \le s_\varepsilon}\|X^\varepsilon_s - x_s\| \le \eta_\varepsilon, \qquad \sup_{t \in [c_\beta\varepsilon^2|\log\varepsilon|,\, t_f]}\big\|X^\varepsilon_{\varepsilon^{-2}t} - q_{\tilde\theta^\varepsilon_t}\big\| \le \varepsilon^\beta,$$

and the dephasing $\big(\tilde\theta^\varepsilon_t - \theta(x_0) - \varepsilon^{-2}t\big)_{t \in [0,t_f]}$ converges in law in $C^0([0,t_f])$ to $\sigma w_t + bt$, with $w$ a standard Brownian motion and

$$\sigma^2 = \frac1T\int_0^T D\theta(q_s)\,G(q_s)G(q_s)^{\top}D\theta(q_s)^{\top}\,ds, \qquad b = \frac1{2T}\int_0^T \mathrm{tr}\big(G(q_s)G(q_s)^{\top}D^2\theta(q_s)\big)\,ds.$$

2. *Drift dominance on longer time scales.* There is $c > 0$ such that if $\varepsilon^2 t_\varepsilon \to \infty$ and $e^{-c\varepsilon^{-2}}t_\varepsilon \to 0$, then the winding number $\mathcal{W}_\varepsilon(t) = \lfloor \tilde\theta^\varepsilon/T \rfloor$ satisfies, in probability,

$$\lim_{\varepsilon\to 0}\frac{\mathcal{W}_\varepsilon(t_\varepsilon) - t_\varepsilon/T}{\varepsilon^2 t_\varepsilon/T} = b.$$

In addition, trajectories started within $\varepsilon^{\beta_0}$ of $M$ stay within $\varepsilon^{\beta_1}$ of $M$ up to times $\exp(\varepsilon^{-\zeta})$ for $\beta_1 < \beta_0$ and $\zeta < 2(1 - \beta_1)$.

## Proof sketch

In isochron coordinates the deterministic dynamics is a rigid rotation, and Itô's formula applied to $\theta(X^\varepsilon)$ gives $d\theta = dt + \varepsilon\,D\theta\,G\,dB + \frac{\varepsilon^2}{2}\mathrm{tr}(GG^\top D^2\theta)\,dt$. On the time scale $\varepsilon^{-2}$ the martingale part accumulates variance $\sigma^2$ per unit time and the Itô correction a drift $b$, both averaged over one turn of the cycle because the process stays $\varepsilon^\beta$-close to $M$. On times $t_\varepsilon \gg \varepsilon^{-2}$ the fluctuations grow like $\sqrt{t_\varepsilon}$ while the drift grows like $t_\varepsilon$, so the frequency shift $\varepsilon^2 b/T$ dominates; the exponential upper bound is the exit time from the basin. Phase reduction of this kind underlies the analysis of noisy neural, circadian and other biological rhythms.

## Sources

- Giambattista Giacomin, Christophe Poquet and Assaf Shapira, "Small noise and long time phase diffusion in stochastic limit cycle oscillators", *Journal of Differential Equations* 264 (2018), 1019–1049, <https://doi.org/10.1016/j.jde.2017.09.029>. Preprint version: arXiv:1512.04436 (2015), Theorem 2.1 (isochron foliation, quoted), Theorems 2.3 and 2.6 (Section 2), Propositions 4.1 and 4.2 (Section 4), <https://doi.org/10.48550/arXiv.1512.04436>.
