# Occupation-time fluctuations of the voter model from a slowly varying initial density

**Setting.** Let $(\eta_t)_{t\ge 0}$ be the voter model on $\mathbb Z^d$: for each site $x$ and each of its $2d$ nearest neighbours $y$, at rate $1$ the opinion at $x$ is replaced by that at $y$. Let $\rho : \mathbb R^d \to (0,1)$ be uniformly continuous, and for $N \ge 1$ let $\nu_{\rho,N}$ be the product measure on $\{0,1\}^{\mathbb Z^d}$ with $\nu_{\rho,N}(\eta(x) = 1) = \rho(x/\sqrt N)$. Start from $\eta_0 \sim \nu_{\rho,N}$ and define the centred occupation time of the origin

$$\xi^N_t = \int_0^t \bigl(\eta_s(\mathbf 0) - \mathbb E_{\nu_{\rho,N}}\eta_s(\mathbf 0)\bigr)\, ds.$$

Let $p_t(x,y)$ be the transition probabilities of continuous-time simple random walk on $\mathbb Z^d$ with generator $\mathcal G g(x) = \sum_{y \sim x}(g(y) - g(x))$, $\gamma_d$ the probability that this walk started at a neighbour of $\mathbf 0$ never hits $\mathbf 0$, and

$$\varrho(t, u) = \mathbb E\, \rho\bigl(\mathcal W_{2t} + u\bigr), \qquad \partial_t \varrho = \Delta \varrho,\ \ \varrho(0,\cdot) = \rho,$$

with $\mathcal W$ a standard Brownian motion on $\mathbb R^d$. Let $h_4(N) = \sqrt{N \log N}$ and $h_d(N) = \sqrt N$ for $d \ge 5$.

**Theorem ($d \ge 4$).** For every $T > 0$, $\bigl\{ h_d(N)^{-1} \xi^N_{tN} \bigr\}_{0 \le t \le T}$ converges weakly in $C[0,T]$ (uniform topology) to the Itô integral $\bigl\{\int_0^t A_{s,d}\, dB_s\bigr\}_{0\le t\le T}$ of a standard Brownian motion $B$, where

$$A_{s,4} = \sqrt{\frac{\gamma_4\, \varrho(s,\mathbf 0)\bigl(1 - \varrho(s,\mathbf 0)\bigr)}{\pi^2}}, \qquad A_{s,d} = \sqrt{4 d \gamma_d \Bigl(\int_0^\infty \theta\, p_{\theta}(\mathbf 0, \mathbf 0)\, d\theta\Bigr) \varrho(s,\mathbf 0)\bigl(1 - \varrho(s,\mathbf 0)\bigr)} \quad (d \ge 5).$$

**Theorem ($d = 3$).** Let $b_t(s,u) = \int_0^{t-s} (4\pi r)^{-3/2} e^{-\|u\|^2/(4r)}\, dr$ for $0 \le s \le t$, $u \in \mathbb R^3$, and let $\zeta$ be the centred continuous Gaussian process with

$$\operatorname{Cov}(\zeta_{t_1}, \zeta_{t_2}) = \int_0^{t_1} \int_{\mathbb R^3} b_{t_1}(s,u)\, b_{t_2}(s,u)\, \varrho(s,u)\bigl(1 - \varrho(s,u)\bigr)\, du\, ds, \qquad 0 \le t_1 \le t_2.$$

Then $\bigl\{N^{-3/4}\xi^N_{tN}\bigr\}_{0\le t\le T}$ converges weakly in $C[0,T]$ to $\bigl\{\sqrt{12\gamma_3}\, \zeta_t\bigr\}_{0\le t\le T}$.

For constant $\rho \equiv p$ both statements reduce to the functional central limit theorems for the homogeneous case (a scaled Brownian motion for $d \ge 4$, and for $d = 3$ a Gaussian process without independent increments).

## Expansion

The local density seen at the origin at macroscopic time $s$ is $\varrho(s, \mathbf 0)$, the heat-equation evolution of the initial profile, because voter-model densities evolve by duality with random walks run at diffusive speed. For $d \ge 4$ one writes $\xi^N$ as a martingale plus a negligible boundary term using the solution of a Poisson equation for the generator (Kipnis-Varadhan method); the martingale's quadratic variation involves $\mathbb E(\eta_{sN}(x) - \eta_{sN}(y))^2$ for neighbours $x \sim y$, which by duality with coalescing random walks and Donsker's invariance principle is close to $2\gamma_d\, \varrho(s,\cdot)(1 - \varrho(s,\cdot))$ near the origin. This converts the constant variance of the homogeneous case into the time-dependent integrand $A_{s,d}^2$. For $d = 3$ the relevant fluctuations are carried by a whole space-time field (Poisson flow method), whose Gaussian limit is driven by the same local variance $\varrho(1-\varrho)$ weighted by the heat-kernel functions $b_t$.

## Sources

- Xiaofeng Xue, "Inhomogeneous central limit theorems for the voter model occupation times", arXiv:2603.07219 (2026), Theorems 2.1 and 2.2 (Section 2), Lemmas 3.1-3.4 and 4.1-4.3, <https://doi.org/10.48550/arXiv.2603.07219>.
