# Expected extinction time of the best class in the tournament ratchet

**Model.** In the Moran tournament ratchet with population size $N$, individuals carry mutation counts $\kappa \in \mathbb{N}_0$; with $N_\kappa$ the number of individuals of type $\kappa$:

- resampling: $(N_\kappa, N_{\kappa'}) \to (N_\kappa + 1, N_{\kappa'} - 1)$ at rate $\frac{1}{2N}N_\kappa N_{\kappa'}$ for $\kappa \ne \kappa'$;
- mutation: $(N_\kappa, N_{\kappa+1}) \to (N_\kappa - 1, N_{\kappa+1} + 1)$ at rate $m N_\kappa$;
- binary tournament selection: $(N_\kappa, N_{\kappa'}) \to (N_\kappa + 1, N_{\kappa'} - 1)$ at rate $\frac{s}{N}N_\kappa N_{\kappa'}$ for $\kappa < \kappa'$ (fitness proportional selection would use rate $\frac{s}{N}N_\kappa N_{\kappa'}(\kappa' - \kappa)$ instead).

Write $\rho = m/s$ for the mutation–selection ratio. The deterministic mutation–selection equilibrium profile $(p_k)$ seen from the best class solves $m(p_k - p_{k-1}) = s\,p_k\big(1 - p_k - 2\sum_{k' < k} p_{k'}\big)$, which has $p_0 > 0$ only if $\rho < 1$, and then $p_0 = 1 - \rho$ (for proportional selection the equilibrium is Haigh's Poisson profile with mean $m/s$). Approximating the size of the best class by the birth–death process $Y$ on $\{0, \dots, N\}$ with rates

$$n \to n-1:\ n\Big(\tfrac12\big(1 - \tfrac nN\big) + m\Big), \qquad n \to n+1:\ n\Big(\tfrac12\big(1 - \tfrac nN\big) + \tfrac{m}{\rho}\big(1 - \tfrac nN\big)\Big),$$

let $T_0$ be its extinction time (the time to the next click of the ratchet).

**Theorem.** Let $1/N \ll m \ll 1$ and $\rho \in [\rho_0, 1)$ for a fixed $\rho_0 \in (0,1)$.

1. *Polynomial regime*, $Nm(1-\rho)^2 \to 0$: if $j_N \ll \sqrt{(N/m)/\log(N/m)}$ then

    $$\mathbb{E}_{j_N}[T_0] \sim 2j_N\Big(\log\sqrt{N/m} - \log j_N\Big),$$

    and if $j_N \gg \sqrt{N/m}$ then $\mathbb{E}_{j_N}[T_0] \sim \frac{\pi^{3/2}}{2}\sqrt{N/m}$.

2. *Exponential regime*, $Nm(1-\rho)^2 \to \infty$ and $1 \ll j_N \le N$:

    $$\mathbb{E}_{j_N}[T_0] \sim \Big(1 - e^{-2m(1/\rho - 1)j_N}\Big)\frac{1}{1-\rho}\sqrt{\frac{\pi}{mN}}\,v_N, \qquad v_N = \frac{\exp\big(2Nm(1-\rho)^2\,\eta(m,\rho)\big)}{m(1/\rho - 1)},$$

    $$\eta(m,\rho) = -\frac{1}{2m}\left[\frac{1}{1-\rho}\log\frac{1+2m}{1+2m/\rho} + \sum_{\ell \ge 1}\Big(1 - (1+2m)^{-\ell}\Big)\frac{(1-\rho)^{\ell-1}}{\ell(\ell+1)}\right].$$

In both regimes the expected number of returns of $Y$ to $(1-\rho)N$ is asymptotically $\frac{1}{m(1-\rho)}$ (polynomial) and $v_N$ (exponential).

## Expansion

The best class fluctuates around its equilibrium size $(1-\rho)N$, with a restoring drift of order $m(1-\rho)$ per individual and neutral noise of order one. When $Nm(1-\rho)^2 \to 0$ the drift is too weak to matter at the scale $\sqrt{N/m}$ and the class behaves like a critical branching process, so clicks occur at polynomial rate. When $Nm(1-\rho)^2 \to \infty$ extinction requires a large deviation against the drift and the click time is exponential in $Nm(1-\rho)^2$; the factor $\eta(m,\rho)$ refines the subcritical logarithmic rate $e^{-2Nm(1/\rho - 1 + \log\rho)}$. The proof is an asymptotic analysis of the Green function of $Y$. Compared with fitness-proportional selection, tournament selection makes the median of the profile play the role that its mean plays in Haigh's analysis, and the near-critical regime $\rho \uparrow 1$ separates the two orders.

## Sources

- Jan Lukas Igelbrink, Adrián González Casanova, Charline Smadi and Anton Wakolbinger, "Muller’s ratchet in a near-critical regime: Tournament versus fitness proportional selection", *Theoretical Population Biology* 158 (2024), 121–138, <https://doi.org/10.1016/j.tpb.2024.06.001>. Numbering as in the preprint arXiv:2306.00471v3, <https://arxiv.org/abs/2306.00471v3>: Definition 2.1 and the mutation–selection equilibrium equations (Section 2), best-class jump rates (Section 3.1) and Theorem 3.4, proved via the Green function in Section 4.1.
