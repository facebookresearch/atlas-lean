# Global threshold of the host-structured coinfection SIS model

**Model.** Host classes $k \in \mathcal{K}$ ($|\mathcal{K}| = p$) have constant size, normalized to $1$. In class $k$ let $S_k, I_k, D_k$ be the proportions susceptible, singly infected and coinfected, with birth-death rate $r_k$, clearance rate $\gamma_k$, transmission rate $\beta_k$ and coinfection factor $\sigma_k > 0$. Class $k$ contacts class $s$ with probability $q_{ks}$, $\sum_s q_{ks} = 1$, and the contact matrix $Q = (q_{ks})$ is irreducible. With force of infection $\Theta_k = \sum_s q_{ks}(I_s + D_s)$,

$$\dot S_k = r_k(1 - S_k) - \beta_k S_k\Theta_k + \gamma_k(I_k + D_k),$$

$$\dot I_k = \beta_k S_k \Theta_k - \sigma_k\beta_k I_k\Theta_k - (\gamma_k + r_k)I_k,$$

$$\dot D_k = \sigma_k\beta_k I_k \Theta_k - (r_k + \gamma_k)D_k .$$

The total prevalence $T_k = I_k + D_k = 1 - S_k$ obeys a closed multi-group SIS system.

**Theorem.** Let $\mathcal{R}_k = \beta_k/(r_k + \gamma_k)$ and $\mathcal{R}_0 = \rho\bigl(\operatorname{diag}(\mathcal{R})\,Q\bigr)$, the spectral radius of the next-generation matrix.
- If $\mathcal{R}_0 \le 1$, the disease-free state $E_0 = \{(1,0,0)\}^p$ is the only equilibrium and is globally stable.
- If $\mathcal{R}_0 > 1$, there is a unique endemic equilibrium, globally and exponentially stable on the state space minus $E_0$, given by

$$S_k^* = \frac{1}{1 + \mathcal{R}_k\Theta_k^*}, \quad T_k^* = \frac{\mathcal{R}_k\Theta_k^*}{1+\mathcal{R}_k\Theta_k^*}, \quad I_k^* = \frac{T_k^*}{1 + \sigma_k\mathcal{R}_k\Theta_k^*}, \quad D_k^* = \frac{\sigma_k\mathcal{R}_k\Theta_k^* T_k^*}{1 + \sigma_k\mathcal{R}_k\Theta_k^*}.$$

Moreover $\operatorname{diag}(\mathcal{R}S^*)\,Q\,T^* = T^*$, so $\rho(\operatorname{diag}(\mathcal{R}S^*)Q) = 1$ at the endemic state.

## Depends on

- [Global asymptotic stability of the SIS endemic equilibrium](../sis-epidemic-model/endemic-globally-asymptotically-stable.md)

## Expansion

Summing the infected compartments removes $\sigma_k$, leaving the classical multi-group SIS model in $T$, which is cooperative and strongly monotone when $Q$ is irreducible; the Lajmanovich-Yorke dichotomy then gives global convergence of $T$. With $T$ (hence $\Theta$) converging, the split of $T_k$ into $I_k$ and $D_k$ follows a linear asymptotically autonomous system whose limit is the stated formula. The endemic fixed-point identity says the effective next-generation matrix, with susceptibles depleted to $S^*$, has spectral radius exactly one.

## Sources

- S. Madec, N. Cinardi, E. Gjini, "Multi-strain SIS dynamics with coinfection under host population structure" (2026), system (SIDS) of Section 2, Propositions 2.2-2.3, Theorem 2.4 and Corollary 2.5, <https://doi.org/10.48550/arXiv.2602.00193>.
