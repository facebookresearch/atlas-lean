# Reproduction number and disease-free stability of the multi-host schistosomiasis model

**Model.** Let $E$ be the number of schistosome eggs, $L$ the number of cercariae, $S_s,S_i$ susceptible and infected snails, and $M_{j,s},M_{j,i}$ susceptible and infected mammals of host type $j=1,\dots,m$. With all parameters positive,

$$E'=\sum_{j=1}^{m}\theta_jM_{j,i}-\omega_sS_sE-\mu_eE,\qquad S_s'=-\omega_s\beta_sS_sE+\alpha_s(S_s+S_i)\Big(1-\frac{S_s+S_i}{\kappa_s}\Big)-\mu_sS_s,\qquad S_i'=\omega_s\beta_sS_sE-(\mu_s+\gamma_s)S_i,$$

$$L'=\nu_sS_i-\sum_{j=1}^{m}\omega_jM_{j,s}L-\mu_lL,\qquad M_{j,s}'=-\omega_j\beta_jLM_{j,s}+\alpha_j-\mu_jM_{j,s},\qquad M_{j,i}'=\omega_j\beta_jLM_{j,s}-(\mu_j+\gamma_j)M_{j,i}.$$

Here $\theta_j$ is egg shedding by infected hosts of type $j$, $\omega_s,\omega_j$ are contact rates of snails with eggs and of mammals with cercariae, $\beta_s,\beta_j$ infection probabilities per contact, $\alpha_s$ and $\kappa_s$ snail growth rate and carrying capacity, $\alpha_j$ mammal recruitment, $\nu_s$ cercarial shedding, and $\mu$'s and $\gamma$'s removal rates. Put $M_j^*=\alpha_j/\mu_j$ and $S^*=\kappa_s(\alpha_s-\mu_s)/\alpha_s$. There are two disease-free equilibria, $DFE_1=(0,0,0,0,M_1^*,0,\dots,M_m^*,0)$ without snails and, when $\alpha_s>\mu_s$, $DFE_2=(0,S^*,0,0,M_1^*,0,\dots,M_m^*,0)$.

**Invariant region.** The box $\Omega$ bounding $E$, $L$, the snail total $S_s+S_i$ by $\max(\kappa_s(\alpha_s-\mu_s),S_0)$ and each mammal total $M_{j,s}+M_{j,i}$ by $\max(\alpha_j/\mu_j,M_0)$ (with the corresponding bounds on $E$ and $L$ in terms of the initial data) is positively invariant, and every initial datum in $\Omega$ has a unique global solution in $\Omega$.

**Reproduction number.**

$$\mathcal R_0=\sum_{j=1}^{m}\Big(\frac{\omega_j\beta_jM_j^*}{\mu_j+\gamma_j}\Big)\Big(\frac{\theta_j}{\mu_e}\Big)\Big(\frac{\omega_s\beta_sS^*}{\mu_s+\gamma_s}\Big)\Big(\frac{\nu_s}{\mu_l}\Big).$$

**Threshold theorem.**

1. If $\alpha_s<\mu_s$, $DFE_1$ is locally and globally asymptotically stable.
2. If $\alpha_s>\mu_s$ and $\mathcal R_0\le1$, $DFE_2$ is locally and globally asymptotically stable.
3. If $\alpha_s>\mu_s$ and $\mathcal R_0>1$, the endemic equilibrium is locally asymptotically stable.

**Optimal control.** Adding time-dependent controls with values in a box $W$ (aquatic control $u_a$ removing eggs and cercariae, molluscicide $u_s$ removing snails, habitat modification $u_\kappa$ acting through the snail carrying capacity, and chemotherapy $u_j$ for infected hosts of the treated types $j\le m_c$) and minimizing

$$J(u)=\int_0^T\Big(\sum_{j=1}^{m_c}M_{j,i}+A_au_a^2+A_su_s^2+A_\kappa u_\kappa^2+\sum_{j=1}^{m_c}A_ju_j^2\Big)dt ,$$

an optimal control exists, and by Pontryagin's principle, with adjoint variables $\lambda_1$ (for $E$), $\lambda_2,\lambda_3$ (snails), $\lambda_4$ (for $L$) and $\lambda_{j,i}$ (infected hosts),

$$u_a^*=\max\Big(0,\min\Big(\frac{\lambda_1E+\lambda_4L}{2A_a},u_{A\max}\Big)\Big),\qquad u_s^*=\max\Big(0,\min\Big(\frac{\lambda_2S_s+\lambda_3S_i}{2A_s},u_{S\max}\Big)\Big),\qquad u_j^*=\max\Big(0,\min\Big(\frac{\lambda_{j,i}M_{j,i}}{2A_j},u_{M\max,j}\Big)\Big).$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The snail subsystem without infection is logistic with net growth $\alpha_s-\mu_s$, which explains the two disease-free states: snails die out when $\alpha_s<\mu_s$ and settle at $S^*$ otherwise. Each factor of $\mathcal R_0$ is one stage of the life cycle: infections of host $j$ per cercaria over its infectious period, eggs shed per infected host over an egg lifetime, snail infections per egg over a snail's infectious period, and cercariae shed per infected snail over a cercarial lifetime; the infection loop passes through every stage once, so the stages multiply and the host types add. Global stability of the disease-free states follows from the Castillo-Chavez type criterion: writing the infected variables $x=(E,S_i,L,M_{1,i},\dots,M_{m,i})$ as $x'=-Ax-f(x,y)$ with $f\ge0$ and the uninfected variables as $y'=g(x,y)$, global attraction of $y'=g(0,y)$ to its disease-free value and the M-matrix property of $A$ give the result. The control formulas come from minimizing the Hamiltonian, which is quadratic in each control, and projecting onto the bounds. The source uses the model to compare control combinations for Lake Mainit, Philippines, where bovines and rodents are reservoir hosts.

## Sources

- J. P. Arcede, B. Doungsavanh, L. A. Estaño and J. C. Jumawan, "Influence of bovines and rodents in the spread of schistosomiasis across the ricefield-lakescape of Lake Mainit, Philippines: an optimal control study", arXiv:2408.05559 (2024), Section 2.1 (model), Section 2.2 (Theorem 2.1, $\mathcal R_0$, Proposition 2.2, Theorem 2.3) and Section 2.3 (Lemmas 2.4 and 2.5, Theorem 2.6), <https://doi.org/10.48550/arXiv.2408.05559>.
