# Kinetic crowd model with disease-state transitions

Let $\Omega \subset \mathbb R^2$ be a walking domain with exits. Pedestrians have position $\mathbf x \in \Omega$, a walking direction $\theta_i = 2\pi (i - 1)/N_\theta$, $i = 1, \dots, N_\theta$, and a disease state $\lambda_j$ in a finite set $I_\lambda$ (for instance $\{S, E, I, R\}$). The distribution function $f_{ij}(t, \mathbf x)$ counts pedestrians at $\mathbf x$ with direction $\theta_i$ and state $\lambda_j$, with local density and compartment totals

$$\rho(t, \mathbf x) = \sum_{j \in I_\lambda} \sum_{i=1}^{N_\theta} f_{ij}(t, \mathbf x), \qquad S(t) = \int_\Omega \sum_{i} f_{iS}(t, \mathbf x)\, d\mathbf x, \ \ldots$$

**Balance equation** (Eqs. 1, 3). With speed $v[\rho]$ depending on the local density and $\mathbf v_i[\rho] = v[\rho]\,(\cos\theta_i, \sin\theta_i)$,

$$\partial_t f_{ij} + \mathrm{div}_{\mathbf x}\big(\mathbf v_i[\rho]\, f_{ij}\big) = \mu[\rho] \Big( \sum_{h=1}^{N_\theta} A_h(i)\, f_{hj} - f_{ij} \Big) + \eta[\rho] \Big( \sum_{s, r \in I_\lambda} \sum_{h, k = 1}^{N_\theta} \mathcal B^{sr}_{hk}(i, j)[\rho]\, f_{hs} f_{kr} - f_{ij}\, \rho \Big).$$

Here $A_h(i)$ is the probability that a walker with direction $\theta_h$ turns to $\theta_i$ because of the geometry (exit, walls), and $\mathcal B^{sr}_{hk}(i, j) = \mathcal B^1_{hk}(i)\, \mathcal B^2_{sr}(j)$ is the probability that a walker in state $(\theta_h, \lambda_s)$ meeting one in state $(\theta_k, \lambda_r)$ moves to $(\theta_i, \lambda_j)$, where $\mathcal B^2_{sr}(j)$ encodes contagion. The rates $\mu$ and $\eta$ (e.g. $\eta[\rho] = \eta_0 \rho$) set the frequencies of interactions with the environment and with other walkers.

**Conservation.** If (Eq. 2)

$$\sum_{i=1}^{N_\theta} A_h(i) = 1, \qquad \sum_{j \in I_\lambda} \sum_{i=1}^{N_\theta} \mathcal B^{sr}_{hk}(i, j) = 1 \quad \text{for all } h, k, s, r,$$

then the interaction terms sum to zero over $(i, j)$, so pedestrians are created or destroyed only through the boundary: $\partial_t \rho + \mathrm{div}_{\mathbf x} \sum_{i,j} \mathbf v_i f_{ij} = 0$.

## Expansion

Summing the first bracket over $i$ and $j$ gives $\sum_{h,j} f_{hj} - \rho = 0$. Summing the second gives $\sum_{h,k,s,r} f_{hs} f_{kr} - \rho^2 = \rho^2 - \rho^2 = 0$. Moments of $f_{ij}$ over directions recover macroscopic compartment densities, so the model couples an [SEIR-type](../seir-epidemic-model/README.md) contagion law to evacuation dynamics in which exposure accumulates where crowding is high, for instance near exits.

## Sources

- J. P. Agnelli, B. Buffa, D. A. Knopoff, et al., *A spatial kinetic model of crowd evacuation dynamics with infectious disease contagion*, Bull. Math. Biol. (2023). <https://doi.org/10.1007/s11538-023-01127-6> (PMCID: PMC9937870)
