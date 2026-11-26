# Spine to explosion and gamma population size near explosion

**Model.** A continuous-time Galton–Watson tree in which each particle branches at rate $1$ into $k \ge 0$ children with probabilities $(p_k)$, whose generating function $f(s) = \sum_k p_k s^k$ satisfies

$$f(s) = s - (1-s)^\alpha L(1-s), \qquad \alpha \in (0,1),$$

with $L : [0,1] \to [0,\infty)$ slowly varying at $0$. Such processes explode (reach infinitely many particles) in finite time $\tau$. Let $N_t$ be the population size and $E(t) = \mathbf{P}(\tau \le t)$ the law of the explosion time; $E$ is regularly varying at $0$ with index $1/(1-\alpha)$, and $1 - E(t) \sim C e^{-(1-p_1)t}$ as $t \to \infty$. Write $\mathbf{P}^T$ for the law conditioned on $\{\tau = T\}$.

**Spine.** Under $\mathbf{P}^T$, for each $t < T$ there is a unique particle $\xi_t$ alive at $t$ with infinitely many descendants at time $T$, the *spine to explosion*.

**Theorem.** Under $\mathbf{P}^T$:
1. *Spinal birth times.* For $0 < s < t$, the number of births by the spine in $[T - t\varepsilon, T - s\varepsilon]$ converges in law as $\varepsilon \downarrow 0$ to a Poisson variable with mean $\frac{\alpha}{1-\alpha}\log(t/s)$; the spine branches at rate $(1+o(1))\frac{\alpha}{1-\alpha}\varepsilon^{-1}$ at time $\varepsilon$ before explosion.
2. *Spinal litter sizes.* The litter $K_\varepsilon$ of a spinal birth at remaining time $\varepsilon$ satisfies $\mathbf{E}^T[e^{-\theta E(\varepsilon)K_\varepsilon}] \to (1+\theta)^{-(1-\alpha)}$, i.e. $E(\varepsilon)K_\varepsilon \Rightarrow \mathrm{Gamma}(1-\alpha, 1)$.
3. *Population size.* $E(\varepsilon) N_{T-\varepsilon} \Rightarrow \mathrm{Gamma}(\alpha, 1)$ as $\varepsilon \downarrow 0$.
4. *Log-time process.* $Z^{\varepsilon,T}_t := E(\varepsilon e^{-t})N_{T - \varepsilon e^{-t}}$ converges in finite-dimensional distributions to a stationary Markov process on $(0,\infty)$ with $\mathrm{Gamma}(\alpha,1)$ marginals and generator $\mathcal{L} = \mathcal{L}_{\mathrm n} + \mathcal{L}_{\mathrm s}$,

$$\mathcal{L}_{\mathrm n}\phi(x) = -\frac{x}{1-\alpha}\phi'(x) + C_\alpha x\int_0^\infty (\phi(x+u) - \phi(x))\,u^{-1-\alpha}e^{-u}\,du,$$

$$\mathcal{L}_{\mathrm s}\phi(x) = C_\alpha \int_0^\infty (\phi(x+u) - \phi(x))\,u^{-\alpha}e^{-u}\,du, \qquad C_\alpha = \frac{\alpha}{\Gamma(2-\alpha)},$$

the non-spine part being a continuous-state branching mechanism and the spine part an immigration.

## Expansion

Conditioning on $\{\tau = T\}$ is a Doob transform by $E'(T - t)$; under it non-spine particles branch at rate $f(v(\varepsilon))/v(\varepsilon)$ and the spine at rate $f'(v(\varepsilon))$, with $v(\varepsilon) = 1 - E(\varepsilon)$, and the spine's litter is size-biased. Regular variation of $E$ converts these rates into the $\varepsilon^{-1}$ scale, so in logarithmic time the spinal births form a homogeneous Poisson process. The rescaled population then solves an affine (CBI) equation whose Laplace transform, $\mathbf{E}[e^{-\theta Z_t} \mid Z_s = x] = e^{-x u_{t-s}(\theta)}\big((1+u_{t-s}(\theta))/(1+\theta)\big)^\alpha$ with $u_r(\theta) = (1 - e^{-r} + e^{-r}(1+\theta)^{1-\alpha})^{1/(1-\alpha)} - 1$, has the gamma law as its fixed point.

## Sources

- Simon C. Harris, Samuel G. G. Johnston and Juan Carlos Pardo, "Behaviour near explosion in continuous-time Galton-Watson trees", arXiv:2610.01810 (2026), Definition 2.1, Theorems 2.2 and 2.3, Propositions 3.1–3.4 and 5.1, <https://doi.org/10.48550/arXiv.2610.01810>.
