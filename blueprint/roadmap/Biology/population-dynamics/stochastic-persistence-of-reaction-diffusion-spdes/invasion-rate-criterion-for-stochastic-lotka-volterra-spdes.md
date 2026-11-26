# Stochastic persistence of competitive Lotka–Volterra SPDEs via invasion rates

**Model.** On a bounded connected smooth domain $D \subset \mathbb{R}^N$, $m$ species with densities $x_i(t, \cdot) \ge 0$ solve

$$dx_i = \Big[d_i \Delta x_i + x_i\Big(m_i - a_{ii} x_i - \sum_{j \ne i} a_{ij} x_j\Big)\Big]dt + \sigma_i(x_i)\, dW_i(t), \qquad \partial_n x_i = 0 \text{ on } \partial D,$$

with constants $d_i > 0$, differentiable functions $a_{ii} > 0$, $a_{ij} \ge 0$, $m_i$ on $\overline D$, $\sigma_i(0) = 0$ (all with bounded Lipschitz derivatives), and independent noises $W_i = \sum_k \lambda_{ik} e_k w_{ik}$, where $(e_k)$ is an orthonormal eigenbasis of $\Delta$ in $L^2(D)$, the $w_{ik}$ are independent Brownian motions and the $\lambda_{ik}$ satisfy a summability condition (for $N = 1$, bounded $\lambda_{ik}$ suffice, which includes space-time white noise). Let $\mathcal{M}_0 = \{x : x_i \equiv 0 \text{ for some } i\}$ be the extinction set.

**Invasion rate.** For an invariant measure $\mu$ on $\mathcal{M}_0$ with $\mu(\{x_k = 0\}) = 1$, consider the process in which species $k$ follows its linearization at $0$,

$$d\tilde x_k = \Big[d_k \Delta \tilde x_k + \tilde x_k\Big(m_k - \sum_{j \ne k} a_{kj} \tilde x_j\Big)\Big]dt + \sigma_k'(0)\, \tilde x_k\, dW_k,$$

and the others follow the full equations without species $k$. With $v_k = \tilde x_k / \|\tilde x_k\|_{L^1}$,

$$r_k(\mu) = \inf_{\nu \in P_k(\mu)} \nu\Big(\int_D v_k\Big(m_k - \sum_{j \ne k} a_{kj}\tilde x_j\Big) - \frac12 \sigma_k'(0)^2 \sum_{i \ge 1} \lambda_{ki}^2 \Big(\int_D e_{i} v_k\Big)^2\Big),$$

where $P_k(\mu)$ is the set of invariant measures of $(v_k, \tilde x_{-k})$ projecting to $\mu$. For general $\mu = p\mu_1 + (1 - p)\mu_2$ with $\mu_1(\{x_k = 0\}) = 1$ and $\mu_2(\{x_k = 0\}) = 0$, set $r_k(\mu) = p\, r_k(\mu_1)$.

**Theorem.** If $\max_i r_i(\mu) > 0$ for every invariant measure $\mu$ supported on $\mathcal{M}_0$, the species coexist:
1. there is an invariant measure $\mu_+$ with $\mu_+(\mathcal{M}_0) = 0$;
2. for every $\delta > 0$ there are $0 < b < B < \infty$ such that for every nonnegative initial condition outside $\mathcal{M}_0$, almost surely

$$\liminf_{T \to \infty} \frac{1}{T}\, \mathrm{Leb}\Big\{t \le T : b \le \int_D x_i(t) \le B \ \text{for all } i\Big\} \ge 1 - \delta.$$

The invasion rates are continuous in $m_i$, $a_{ij}$ and $\sigma_i$, so coexistence survives small perturbations.

## Expansion

The quantity inside $\nu(\cdot)$ is Itô's formula for $\ln \int_D x_k$ evaluated at $x_k = 0$, so $r_k(\mu)$ is the long-run exponential growth rate of a rare invader of species $k$ into the community state $\mu$. The theorem is the infinite-dimensional analogue of the finite-dimensional invasion-rate criterion for stochastic Kolmogorov systems: if on every invariant state of the boundary some missing species can invade, a weighted sum of $-\ln \int_D x_i$ is a Lyapunov function pushing the process away from $\mathcal{M}_0$. The infinite dimension costs tightness of occupation measures, which is supplied by smoothing estimates for the Neumann heat semigroup.

## Sources

- J. Foldes, D. Stacy, "Stochastic Persistence in Infinite Dimensions", arXiv:2601.19145 (2026), Theorem 24 (general criterion), Section 7.4: Definition 128 and Theorem 133, <https://doi.org/10.48550/arXiv.2601.19145>.
