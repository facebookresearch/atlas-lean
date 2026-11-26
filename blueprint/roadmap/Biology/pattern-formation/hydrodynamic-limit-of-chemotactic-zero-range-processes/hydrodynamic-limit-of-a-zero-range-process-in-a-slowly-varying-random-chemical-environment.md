# Hydrodynamic limit of a zero-range process in a slowly varying random chemical environment

**Particle system.** On the discrete torus $\mathbb{T}^d_N = \{1,\dots,N\}^d$, embedded in $\mathbb{T}^d = \mathbb{R}^d/\mathbb{Z}^d$ by $x \mapsto x/N$, a configuration $\eta(x) \in \mathbb{N}$ counts cells at site $x$. Cells perform symmetric nearest-neighbour jumps: from site $x$ one cell jumps to a given neighbour at rate $N^2 g(\eta(x))\,p^N_x$ (diffusive time scaling), where the environment is

$$p^N_x = v(x/N) + q_x,$$

with $v \in C^1(\mathbb{T}^d)$ the slowly varying mean of the chemical field and $(q_x)_{x\in\mathbb{Z}^d}$ a uniformly bounded, stationary, ergodic, mean-zero random field of law $m$, with $p^N_x, q_x \in [a,b]$, $0 < a < b$. The rate function $g$ satisfies $g(n) = 0 \iff n = 0$, is uniformly Lipschitz ($\sup_n|g(n+1) - g(n)| < \infty$) and grows at least linearly ($\inf_n g(n)/n > 0$).

**Invariant measures and macroscopic flux.** The process has product invariant measures $\nu^{N,p}_\varphi(\eta) = \prod_x \big[(p^N_x)^{-1}\varphi\big]^{\eta(x)} / \big(Z((p^N_x)^{-1}\varphi)\,g(\eta(x))!\big)$, with $g(n)! = g(1)\cdots g(n)$ and $Z(\varphi) = \sum_n \varphi^n/g(n)!$. Let $M(\varphi)$ be the mean of the one-site marginal $\varphi^n/(Z(\varphi)g(n)!)$, and

$$R(u,\varphi) = \mathbb{E}_m\Big[M\Big(\frac{\varphi}{v(u) + q_0}\Big)\Big],$$

strictly increasing in $\varphi$, with inverse $\Phi(u,\cdot)$.

**Theorem.** Suppose the initial laws $\mu^N_0$ have a profile $\rho_0 \in L^\infty(\mathbb{T}^d)$, i.e. $N^{-d}\sum_x G(x/N)\eta(x) \to \int G\rho_0$ in probability for all $G \in C(\mathbb{T}^d)$, and satisfy the entropy bound $H(\mu^N_0 \mid \nu^{N,p}_\varphi) \le CN^d$ and $\mathbb{E}_{\mu^N_0}\big[\sum_x \eta(x)^2\big] \le CN^d$. Then, for $m$-almost every environment, all $t > 0$, $G \in C(\mathbb{T}^d)$ and $\delta > 0$,

$$\lim_{N\to\infty}\mu^N_t\Big(\Big|\frac{1}{N^d}\sum_{x\in\mathbb{T}^d_N} G(x/N)\eta(x) - \int_{\mathbb{T}^d} G(u)\rho_t(u)\,du\Big| \ge \delta\Big) = 0,$$

where $\rho_t$ solves $\partial_t\rho_t(u) = \Delta\,\Phi(u,\rho_t(u))$.

**Corollary (independent walkers).** If $g(n) = n$ and cells jump at rate $N^2 f(\zeta(x))$ with $f \colon \mathbb{N} \to [a,b]$, where the chemical molecule counts $\zeta(x)$ are independent Poisson variables of mean $\vartheta(x/N)$, then the cell density converges to the solution of

$$\partial_t\rho = \Delta\big[\tilde f(\vartheta(u))\rho\big] = \nabla\cdot\big[\tilde f(\vartheta)\nabla\rho + \tilde f'(\vartheta)\rho\nabla\vartheta\big], \qquad \tilde f(\vartheta) = \mathbb{E}\big[1/f(\zeta)\big]^{-1},$$

a Keller–Segel cell equation in a fixed chemical landscape; cells that linger where the signal is high (small $f$) drift up the mean signal gradient, although they only sense local concentrations.

## Expansion

The proof adapts the entropy method of Guo–Papanicolaou–Varadhan: relative entropy with respect to the local-equilibrium product measures stays of order $N^d$, which gives tightness and a one- and two-block replacement lemma. Because the mean $v$ varies on the macroscopic scale, the environment is locally an ergodic random medium, so the homogenization arguments for zero-range processes in ergodic environments apply in small boxes, while the slow variation produces the explicit $u$-dependence of $\Phi$. In a stationary chemical field no blow-up can occur, so this limit captures the drift but not the aggregation feedback of the full Keller–Segel system.

## Sources

- S. Großkinsky, D. Marahrens and A. Stevens, "A hydrodynamic limit for chemotaxis in a given heterogeneous environment", arXiv:1508.03569 (2015), Theorem 2.1 with Assumption 1, Corollary 1.1 and Remark 1.2, proof in Section 3, <https://doi.org/10.48550/arXiv.1508.03569>.
