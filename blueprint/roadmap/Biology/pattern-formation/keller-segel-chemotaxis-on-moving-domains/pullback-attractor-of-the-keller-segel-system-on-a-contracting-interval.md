# Pullback attractor of the Keller–Segel system on a contracting interval

**Model.** Let $\alpha(t)<\beta(t)$, $\gamma(t)=\beta(t)-\alpha(t)$ and $\mathcal{I}_t=(\alpha(t),\beta(t))$. For constants $a,b,c,d,\kappa>0$ consider the one-dimensional Keller–Segel system for cell density $u$ and chemoattractant $\rho$ on the moving interval:

$$u_t=a\,u_{xx}-\kappa\,(u\rho_x)_x,\qquad \rho_t=b\,\rho_{xx}+c\,u-d\,\rho,\qquad x\in\mathcal{I}_t,\ t>\tau,$$

with homogeneous Neumann conditions $u_x=\rho_x=0$ at $x\in\{\alpha(t),\beta(t)\}$ and data $(u_\tau,\rho_\tau)\ge 0$ at time $\tau\in\mathbb{R}$.

**Hypotheses.** (H1) $\alpha,\beta\in C^1(\mathbb{R})$ and $0<\gamma_0<\gamma(t)<\gamma_1$. (H2) the domain contracts: $\alpha'\ge0$, $\beta'\le0$. (H3) $\alpha',\beta'\in L^\infty(\mathbb{R})$. (H4) small gain: for a specific constant $C>0$ and some $\theta\in(0,1)$,

$$C\,\gamma_1\big(\|\alpha'\|_{\infty}+\|\gamma'\|_{\infty}\big)\,\Gamma(1-\theta)<1 .$$

**Theorem.**
1. Under (H1)–(H2), for every $(u_\tau,\rho_\tau)\in L^2(\mathcal{I}_\tau)\times H^1(\mathcal{I}_\tau)$, $u_\tau,\rho_\tau\ge 0$, there is a unique nonnegative global weak solution, and the total mass is nonincreasing:

$$\int_{\mathcal{I}_t}u(x,t)\,dx\le\int_{\mathcal{I}_\tau}u_\tau(x)\,dx .$$

2. Under (H1)–(H4), on the phase spaces $\mathbb{H}^M_{1,t}=\{(u,\rho)\in L^2(\mathcal I_t)\times H^1(\mathcal I_t):u,\rho\ge0,\ \int u\le M\}$ the solution process is dissipative with an explicit exponential decay rate, and it has a minimal pullback attractor $\{\mathcal{A}(t)\}_{t\in\mathbb{R}}$ in the universe of families of bounded sets, contained in a ball of radius $R_M$ independent of $t$. Transporting it to the fixed reference interval by the rescaling map gives the minimal pullback attractor of the rescaled problem.

## Expansion

The change of variables $y=(x-\alpha(t))/\gamma(t)$ together with a time reparametrization turns the problem into a semilinear system on a fixed interval with time-independent principal part and nonautonomous transport terms of size $\|\alpha'\|_\infty+\|\gamma'\|_\infty$. Integrating the $u$ equation gives $\frac{d}{dt}\int_{\mathcal I_t}u=\beta'u(\beta)-\alpha'u(\alpha)\le0$ under contraction, the only source of a uniform mass bound once mass conservation is lost. The transport terms are controlled through a singular Gronwall inequality with a singular kernel $(t-s)^{-\theta}$ damped by an exponential factor; the small gain condition (H4), in which $\Gamma(1-\theta)=\int_0^\infty\sigma^{-\theta}e^{-\sigma}d\sigma$ is the kernel's total weight, makes the feedback gain less than one, which yields absorbing sets uniform in the initial time, where the classical Henry inequality would only give finite-time bounds.

## Sources

- Jackeline C. Huaccha Neyra, John Matos Ascona, Lizet Santa Cruz Calderón and Heraclio López-Lázaro, "A Keller--Segel Chemotaxis Model on One-Dimensional Moving Domains", arXiv:2611.30752 (2026), hypotheses (H1)–(H4) of Section 1, Theorem 3.8 (global weak solutions), Lemma 2.22 (damped singular Gronwall inequality) and Theorems 4.5 and 4.9 (pullback attractors), <https://doi.org/10.48550/arXiv.2611.30752>.
