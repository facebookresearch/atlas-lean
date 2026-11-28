# Epidemic threshold of SIS with contact, local and global awareness

**Model.** An SIS infection spreads on an uncorrelated network with degree distribution $P(k)$, $k = 1, \dots, n$, mean degree $\langle k \rangle$, and recovery rate $\gamma = 1$. The infection rate along an edge from an infectious node $j$ to a susceptible node $i$ is $q_{ij} = A_i T_j$ with transmission rate $T_j = \lambda$ and admission rate

$$A_i = \psi(k_i)\left(1 - \alpha\,\frac{k^{\mathrm{inf}}_i}{k_i}\right)\big(1 - \beta\,\rho(t)\big),$$

where $\psi$ is a positive non-increasing function of the degree (contact awareness), $k^{\mathrm{inf}}_i$ the number of infected neighbours of $i$, $\alpha \in [0,1]$ the strength of local awareness, $\rho(t)$ the overall prevalence and $\beta \in [0,1]$ the strength of global awareness. With $\rho_k$ the prevalence among degree-$k$ nodes and $\Theta = \sum_k kP(k)\rho_k/\langle k\rangle$ the probability that a random edge points to an infected node, the heterogeneous mean-field equations are

$$\frac{d\rho_k}{dt} = -\rho_k + \lambda k\, \psi(k)(1-\rho_k)\,\Theta(1 - \alpha\Theta)(1 - \beta\rho) - \lambda\alpha\,\psi(k)(1-\rho_k)(1-\beta\rho)\,\Theta(1-\Theta),$$

with $\rho = \sum_k P(k)\rho_k$.

**Theorem.** Assume $\langle k^2\psi(k)\rangle > \alpha\langle k\psi(k)\rangle$. The infection-free equilibrium $\rho_k \equiv 0$ is locally asymptotically stable if $\lambda < \lambda_c$ and unstable if $\lambda > \lambda_c$, where

$$\lambda_c = \frac{\langle k \rangle}{\langle k^2 \psi(k) \rangle - \alpha\,\langle k\, \psi(k) \rangle}.$$

In particular $\lambda_c$ does not depend on the global awareness $\beta$, is increasing in the local awareness $\alpha$, and for $\alpha = 0$, $\psi \equiv 1$ reduces to the classical threshold $\lambda_c = \langle k\rangle / \langle k^2 \rangle$.

**Lemma (rank-one perturbation of a diagonal matrix).** If $a_{ij} = \delta_{ij}\upsilon_i + \sigma_i l_j$ then

$$\det[a_{ij}] = \prod_{i=1}^n \upsilon_i + \sum_{i=1}^n \sigma_i l_i \prod_{m \ne i} \upsilon_m .$$

## Expansion

The binomial number $s$ of infected neighbours of a degree-$k$ node has $\mathbb E[s] = k\Theta$ and $\mathbb E[s^2] = k^2\Theta^2 + k\Theta(1-\Theta)$, which gives the drift above. Dropping terms of order two in $\rho_k$ leaves $\dot\rho_k = -\rho_k + \lambda(k - \alpha)\psi(k)\Theta$; its Jacobian is $J_0 = -I + \sigma l^\top$ with $\sigma_k = \lambda(k-\alpha)\psi(k)$ and $l_k = kP(k)/\langle k\rangle$. By the lemma with $\upsilon_k = -1-\mu$,

$$\det(J_0 - \mu I) = (-1-\mu)^{n-1}\Big(-1-\mu+\sum_k \sigma_k l_k\Big),$$

so $n-1$ eigenvalues equal $-1$ and the dominant one is $\mu_n = \sum_k \sigma_k l_k - 1 = \lambda\big(\langle k^2\psi\rangle - \alpha\langle k\psi\rangle\big)/\langle k\rangle - 1$, whose sign change gives $\lambda_c$. The global factor $(1-\beta\rho)$ equals $1$ at the infection-free state and so drops out of the linearisation, although it reduces the endemic prevalence. With $\psi(k) = k^{-b}$ on scale-free networks, a stronger contact awareness ($b$ larger) shrinks $\langle k^{2-b}\rangle$ and raises the threshold.

## Sources

- Q. Wu, X. Fu, M. Small, X.-J. Xu, "The impact of awareness on epidemic spreading in networks", Chaos 22 (2012) 013101, Section II (admission rate, Eq. 2; mean-field equations, Eq. 9) and Section III (Lemma 1, Jacobian $J_0$, threshold Eq. 11), <https://doi.org/10.1063/1.3673573> (PMC7112450).
