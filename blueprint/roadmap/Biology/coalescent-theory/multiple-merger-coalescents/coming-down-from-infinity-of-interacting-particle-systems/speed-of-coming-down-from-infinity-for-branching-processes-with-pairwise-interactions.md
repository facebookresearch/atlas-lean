# Speed of coming down from infinity for subcritical branching processes with pairwise interactions

**Model.** A branching process with pairwise interactions (BPI process) is a continuous-time Markov chain on $\mathbb{N}_0$ with parameters $c, d \ge 0$ and nonnegative sequences $(\pi_i)_{i \ge 1}$, $(b_i)_{i \ge 1}$ with $\rho = \sum_i \pi_i < \infty$ and $b = \sum_i b_i < \infty$. From state $z \ge 1$ it jumps

$$z \to z + i \text{ at rate } z\pi_i + z(z-1) b_i \quad (i \ge 1), \qquad z \to z - 1 \text{ at rate } d z + c z(z-1).$$

The linear terms are ordinary branching and death; $c z(z-1)$ is pairwise competition and $b z(z-1)$ pairwise cooperation (a pair produces $i$ offspring with probability $b_i/b$). With $c > 0$ and $b = \pi = d = 0$ it is the block-counting process of Kingman's coalescent; $b = 0$ gives the logistic branching process. Set

$$\mathbf{m}_{\rm int} = -c + \sum_{i \ge 1} i\, b_i, \qquad \boldsymbol{\sigma}^2_{\rm int} = c + \sum_{i\ge1} i^2 b_i;$$

the process is *subcritical cooperative* when $\mathbf{m}_{\rm int} < 0$.

**Theorem.** Assume $\mathbf{m}_{\rm int} < 0$, $\sum_i i\pi_i < \infty$, and $\sum_i i^\alpha b_i < \infty$ for some $\alpha \in (1,2]$.
1. As $z \to \infty$ the BPI processes $Z^{(z)}$ converge weakly in $\mathbb{D}(\mathbb{R}_+, \overline{\mathbb{R}})$ to a BPI process $Z^{(\infty)}$ started from $\infty$, which comes down from infinity, $\mathbb{P}(Z^{(\infty)}_t < \infty \ \forall t > 0) = 1$, at speed

$$\lim_{t \downarrow 0} (-\mathbf{m}_{\rm int})\, t\, Z^{(\infty)}_t = 1 \quad \text{almost surely}.$$

2. If moreover $\sum_i \vartheta^i \pi_i < \infty$ and $\sum_i \vartheta^i b_i < \infty$ for some $\vartheta > e^{288}$, the convergence also holds in $L^p$, $p \in (0,2]$: $\mathbb{E}\big[\sup_{s \le t} |-\mathbf{m}_{\rm int}\, s Z^{(\infty)}_s - 1|^p\big] \to 0$ as $t \downarrow 0$.
3. *(Second-order fluctuations.)* Under the same exponential moments, with $X^{(\varepsilon)}_t = \varepsilon^{-1/2}\big(-\mathbf{m}_{\rm int}\,\varepsilon t\, Z^{(\infty)}_{\varepsilon t} - 1\big)$, $X^{(\varepsilon)}$ converges weakly in $\mathbb{D}(\mathbb{R}_+, \mathbb{R})$ as $\varepsilon \downarrow 0$ to the centered Gaussian process

$$X_0 = 0, \qquad X_t = \frac{\boldsymbol{\sigma}_{\rm int}}{t}\int_0^t u\, dW_u \quad (t > 0),$$

with $W$ a standard Brownian motion.

For Kingman's coalescent ($\mathbf{m}_{\rm int} = -c$) part 1 recovers the classical $N_t \sim 1/(ct)$ for the number of blocks.

## Depends on

- [The speed of coming down from infinity](../speed-of-coming-down-from-infinity/speed.md)

## Expansion

For a huge population the quadratic interactions dominate, and the mean jump from $z$ is about $\mathbf{m}_{\rm int} z^2$, so $\dot z = \mathbf{m}_{\rm int} z^2$, giving $z(t) = 1/(-\mathbf{m}_{\rm int} t)$ from $z(0) = \infty$. Linear branching is negligible at this scale. The moment condition with $\alpha > 1$ controls large cooperative jumps so that a martingale argument for $1/Z$ works. The fluctuation is a central limit theorem for that martingale: the quadratic variation of the jumps of $1/Z$ accumulates like $\boldsymbol\sigma^2_{\rm int} u^2\,du$ in rescaled time, giving the time-averaged Gaussian process.

## Sources

- Gabriel Berzunza Ojeda and Juan Carlos Pardo, "On the speed of coming down from infinity for subcritical branching processes with pairwise interactions", Stoch. Process. Appl. 201 (2026), 105036, <https://doi.org/10.1016/j.spa.2026.105036>. Numbering follows the arXiv version, arXiv:2501.06684 (2025): Section 1 generator and Theorems 2.1–2.3, <https://doi.org/10.48550/arXiv.2501.06684>.
