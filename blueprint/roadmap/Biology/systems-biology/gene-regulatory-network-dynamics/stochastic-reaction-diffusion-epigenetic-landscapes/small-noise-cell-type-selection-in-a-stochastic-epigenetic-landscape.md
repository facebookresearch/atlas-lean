# Small-noise cell-type selection in a stochastic epigenetic landscape

**Landscape.** An epigenetic landscape on the plane of two expression variables $(u,v)$ has four basins (cell types) with centers $(u_k,v_k)$ and sizes $a_k > 0$:

$$F(u,v) = \min_{1\le k\le4}\, a_k\big[(u-u_k)^2 + (v-v_k)^2\big],$$

used through a smooth mollification $F_\varepsilon$ (of class $C^3$, coercive, with isolated minima and positive-definite Hessians at the minima). Let $\tilde f = -\partial_u F_\varepsilon$, $\tilde g = -\partial_v F_\varepsilon$.

**Stochastic model.** On a one-dimensional tissue $\mathcal O = [0,R]$ (periodic, i.e. the circle $\mathbb T$, or Neumann conditions),

$$\partial_t u = d_1\partial_x^2 u + \tilde f(u,v) + \sigma w_1, \qquad \partial_t v = d_2\partial_x^2 v + \tilde g(u,v) + \sigma w_2,$$

with $d_1, d_2 > 0$ and independent space-time white noises $w_1, w_2$ of equal intensity $\sigma > 0$.

**Theorem.** For continuous initial data:

1. The system has a unique generalized solution, which is a Markov–Feller process on $C(\mathbb T;\mathbb R^2)$ with a unique normalized stationary measure $\nu^\sigma$; for every Borel set $\Gamma$ and every initial state, the fraction of time spent in $\Gamma$ converges almost surely to $\nu^\sigma(\Gamma)$.
2. With $\hat\varphi^{(k)} = (u_k,v_k)$ the four absolute minima of $F$ and $\Delta_k = \det\mathbf H(F)(\hat\varphi^{(k)}) = 4a_k^2$, the measures $\nu^\sigma$ converge weakly as $\sigma \to 0$ to the measure concentrated on the constant states $\hat\varphi^{(k)}$ with weights

$$\nu^0\big(\hat\varphi^{(k)}\big) = \frac{\Delta_k^{-1}}{\sum_{j=1}^4\Delta_j^{-1}}.$$

3. Each constant state $\varphi_0 \equiv \hat\varphi^{(k)}$ is an asymptotically stable equilibrium of the noiseless system, and the corresponding phenotype regions are invariant. If $D \subset C(\mathbb T;\mathbb R^2)$ is a regular region containing $\varphi_0$ whose deterministic trajectories stay in $D$ and converge to $\varphi_0$, and

$$U(\varphi) = \int_{\mathbb T}\Big[\tfrac12\sum_{k=1}^2 d_k\big(\varphi_k'(x)\big)^2 + F(\varphi(x))\Big]dx,$$

then the exit time $\tau^\sigma$ of the process from $D$ satisfies, for $g \in D$,

$$\lim_{\sigma\to0^+}\sigma^2\ln\mathbb E_g\tau^\sigma = 2\min_{\varphi\in\partial D}\big(U(\varphi) - U(\varphi_0)\big).$$

Narrow basins (large $a_k$) are selected less often in the small-noise limit, and transitions between cell types occur through mountain-pass configurations of the tissue energy $U$.

## Expansion

The drift is the gradient of $-U$ in $L^2$, so for equal noise intensities the system is a gradient SPDE whose stationary law is formally proportional to $\exp(-2U/\sigma^2)$. All four minima have $F = 0$, so as $\sigma \to 0$ the competition between constant states is decided by the Gaussian fluctuation volume around each minimum, which is inversely proportional to the Hessian determinant $\Delta_k$. The exit-time asymptotics are the Freidlin–Wentzell large-deviation estimate for reaction–diffusion equations perturbed by white noise, with quasi-potential given by the energy barrier $U(\varphi) - U(\varphi_0)$. A companion part of the paper derives stochastic maximum principles for controlled versions of the model.

## Sources

- Pablo Padilla-Longoria, Jesús Sierra, "On a stochastic PDE model for epigenetic dynamics", arXiv (2024). Section 2 (landscape $F$ and stochastic epigenetic system), Section 3 (Theorem 1; Theorems 2–3 on optimal control), Section 4 (Proposition 1). <https://doi.org/10.48550/arXiv.2401.03596>. Published version: Journal of Nonlinear Science 36(4) (2026), article 93, <https://doi.org/10.1007/s00332-026-10312-5>; locators above refer to the arXiv version.
