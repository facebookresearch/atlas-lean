# Real-time growth and extinction of the effective-degree network epidemic

**Model.** $N$ individuals form a configuration-model network with degree law $p_k = \mathbb{P}(D = k)$, $k \le k_{\max}$, mean $\mu_D$, and size-biased law $\tilde p_k = k p_k/\mu_D$ (the degree $\tilde D$ of a neighbor). Infectives recover at rate $\gamma$ and transmit along each edge to a susceptible neighbor at rate $\tau$. Building the network as the epidemic progresses, an infective of type $k$ is one with $k$ unpaired stubs. For large $N$ the early epidemic is a continuous-time multitype branching process $\mathbf{Z}(t) = (Z_k(t))_{k \le k_{\max}}$: a type-$k$ individual recovers at rate $\gamma$, and at rate $\tau k$ it uses a stub, becoming type $k-1$ and creating a new infective of type $l$ with probability $\tilde p_{l+1}$ (its remaining stubs).

**Mean behavior.** The mean matrix $\mathbf{M}(t) = [\mathbb{E}Z^{(i)}_j(t)]$ satisfies $\mathbf{M}' = \mathbf{M}\boldsymbol\Omega$, $\mathbf{M}(0) = \mathbf{I}$, with $\Omega_{l,k} = \tau l(\tilde p_{k+1} + \delta_{l,k+1}) - (\gamma + \tau l)\delta_{l,k}$, so $\mathbf{M}(t) = e^{\boldsymbol\Omega t}$. The eigenvalues of $\boldsymbol\Omega$ are $-\gamma - i\tau$ for $i \in \{0, 2, 3, \dots, k_{\max}\}$ and the dominant one

$$r = \tau\big(\mathbb{E}[\tilde D] - 2\big) - \gamma = \tau\mu_{\tilde D - 2} - \gamma,$$

the real-time (Malthusian) growth rate: the process dies out almost surely if $r \le 0$, and grows like $e^{rt}$ on survival if $r > 0$. With $\mathbf{n} = (k)_k$ the vector of types,

$$\mathbf{m}(t) = \mathbb{E}\,\mathbf{Z}(t) = \mu_{\tilde D - 2}^{-1}\big(e^{rt} - e^{-\gamma t}\big)\mathbf{n} + e^{-\gamma t}\mathbf{1}, \qquad \lim_{t\to\infty} e^{-rt}\mathbf{m}(t) = \mu_{\tilde D - 2}^{-1}\mathbf{n},$$

where $\mathbf{m}(t)_k$ is the expected total number of infectives at time $t$ starting from one infective of type $k$. Mean prevalence therefore approaches exponential growth at rate $r + \gamma$, with prefactor equal to the initial infective's degree divided by $\mu_{\tilde D - 2}$.

**Extinction.** The probabilities $\pi_k(t) = \mathbb{P}(Z^{(k)}(t) = 0)$ solve

$$\frac{d}{dt}\pi_k = -(\gamma + \tau k)\pi_k + \gamma + \tau k\,\pi_{k-1}\sum_{l=0}^{k_{\max}-1}\tilde p_{l+1}\pi_l,$$

and in the subcritical case $r < 0$ the survival probability obeys $1 - \pi_k(t) \le k\,\mu_{\tilde D - 2}^{-1}(e^{rt} - e^{-\gamma t}) + e^{-\gamma t}$ (also for unbounded degrees with $\mathbb{E}\tilde D < \infty$).

## Depends on

- [Generation sizes of the branching process](../../branching-process-approximation-of-early-epidemi/bp-size.md)

## Expansion

The forward Kolmogorov equations give the linear system for $\mathbf{M}$. Two vectors span an invariant subspace: $\boldsymbol\Omega\mathbf{1} = -\gamma\mathbf{1} + \tau\mathbf{n}$ (every stub use creates one infective) and $\boldsymbol\Omega\mathbf{n} = r\mathbf{n}$ (stubs are consumed at rate $\tau$ per stub and created at rate $\tau(\mathbb{E}\tilde D - 1)$, while recovery removes them at rate $\gamma$). For any matrix with $\mathbf{M}\mathbf{x} = a\mathbf{x} + b\mathbf{y}$ and $\mathbf{M}\mathbf{y} = c\mathbf{y}$ ($a \ne c$), $e^{\mathbf{M}t}\mathbf{x} = e^{at}\mathbf{x} + \frac{b}{a - c}(e^{at} - e^{ct})\mathbf{y}$; with $a = -\gamma$, $b = \tau$, $c = r$ and $r + \gamma = \tau\mu_{\tilde D - 2}$ this gives $\mathbf{m}(t)$ exactly. The extinction equations are the backward equations $\pi_k' = -\omega_k\pi_k + \omega_k P_k(\boldsymbol\pi)$ with event rate $\omega_k = \gamma + \tau k$ and offspring generating function $P_k$; Markov's inequality $\mathbb{P}(Z > 0) \le \mathbb{E}Z$ applied to the exact mean gives the subcritical bound. The condition $r > 0$ is equivalent to the classical network threshold $R_0 = \frac{\tau}{\tau + \gamma}(\mathbb{E}\tilde D - 1) > 1$, while $r$ itself measures real-time speed.

## Sources

- Frank Ball, Thomas House, "Heterogeneous network epidemics: real-time growth, variance and extinction of infection", Journal of Mathematical Biology 75 (2017), 577–619, <https://doi.org/10.1007/s00285-016-1092-3>. Published version of arXiv:1601.07415, cited next; locators there refer to the arXiv version.
- Frank Ball, Thomas House, "Heterogeneous network epidemics: real-time growth, variance and extinction of infection", arXiv (2016). Section 2 (model, effective-degree construction, branching process), Section 3 (Proposition 1 and the mean equations), Section 7 (probability of extinction), Appendix B (eigenvalues). <https://doi.org/10.48550/arXiv.1601.07415>
