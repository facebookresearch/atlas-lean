# Control matrices of a network with conserved pools

At a regular steady state with fixed conserved pools, concentration and flux responses to enzyme levels are given by the control matrices $-BJ_{\mathrm{red}}^{-1}N_R$ and $I-\varepsilon'BJ_{\mathrm{red}}^{-1}N_R$ built from the reduced Jacobian.

Let $M,R$ be finite, $N\in\mathbb{R}^{M\times R}$ with a [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$, $N=BN_R$, rate laws $f_i$ with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$, and let $\sigma$ be a [regular steady state with pool totals](conserved-pool-regular-steady-state.md) $T$ at $e_0$. Write $s_0=\sigma(e_0)$, $\varepsilon'=\varepsilon'(e_0,s_0)$, $J_{\mathrm{red}}=N_R\varepsilon'B$ (invertible by hypothesis), and $v^0=J(e_0)=v(e_0,s_0)$ for the [steady-state fluxes](../steady-flux.md) $J(e)=v(e,\sigma(e))$. Define the **unscaled control matrices**

$$C^{s\prime}=-B\,J_{\mathrm{red}}^{-1}N_R\in\mathbb{R}^{M\times R},\qquad C^{J\prime}=I_R-\varepsilon'B\,J_{\mathrm{red}}^{-1}N_R\in\mathbb{R}^{R\times R}.$$

Then for all $i,j\in R$ and $m\in M$:

1. $e_{0,i}\,\dfrac{\partial\sigma_m}{\partial e_i}(e_0)=C^{s\prime}_{mi}\,v^0_i$ and $e_{0,i}\,\dfrac{\partial J_j}{\partial e_i}(e_0)=C^{J\prime}_{ji}\,v^0_i$;
2. the [concentration control coefficients](../conc-control.md) are $C^{s_m}_{e_i}=C^{s\prime}_{mi}v^0_i/s_{0,m}$ when $s_{0,m}\ne0$, and the [flux control coefficients](../flux-control.md) are $C^{J_j}_{e_i}=C^{J\prime}_{ji}v^0_i/v^0_j$ when $v^0_j\ne0$;
3. $LC^{s\prime}=0$: first-order concentration responses leave every pool total unchanged;
4. $C^{s\prime}$ and $C^{J\prime}$ do not depend on the choice of $(B,L)$.

These identities hold for any such $\sigma$, whether or not it was produced by the [regular steady-state existence theorem](exists-conserved-pool-steady-state-map.md); they use only the steady-state and pool identities near $e_0$ and differentiability at $e_0$.

## Depends on

- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Reaction fluxes proportional to enzyme levels](../flux.md)
- [Steady-state fluxes along a steady-state map](../steady-flux.md)
- [Concentration control coefficient](../conc-control.md)
- [Flux control coefficient](../flux-control.md)

## Proof depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Concentration control coefficient](../conc-control.md)
- [Flux control coefficient](../flux-control.md)

## Expansion

Each $v_i(e,s)=e_if_i(s)$ is differentiable at $(e_0,s_0)$, so the chain rule applies to $e\mapsto N_Rv(e,\sigma(e))$, which vanishes near $e_0$:

$$N_R\bigl(\operatorname{diag}(f(s_0))+\varepsilon'D\sigma(e_0)\bigr)=0 .$$

Differentiating $L\sigma=T$ gives $LD\sigma(e_0)=0$, so every column of $D\sigma(e_0)$ lies in $\ker L=\operatorname{im}B$ and $D\sigma(e_0)=BZ$ for a unique $Z\in\mathbb{R}^{q\times R}$. Substituting, $J_{\mathrm{red}}Z=-N_R\operatorname{diag}(f(s_0))$, hence $D\sigma(e_0)=-BJ_{\mathrm{red}}^{-1}N_R\operatorname{diag}(f(s_0))$; multiplying on the right by $\operatorname{diag}(e_0)$ turns $\operatorname{diag}(f(s_0))$ into $\operatorname{diag}(v^0)$. For fluxes, $DJ(e_0)=\operatorname{diag}(f(s_0))+\varepsilon'D\sigma(e_0)$, and the same right multiplication gives item 1. Item 2 is the definition of the scaled coefficients. Item 3 is $LB=0$. Item 4: with $B'=BP$, $N_R'=P^{-1}N_R$ one has $B'(P^{-1}J_{\mathrm{red}}P)^{-1}N_R'=BJ_{\mathrm{red}}^{-1}N_R$.

These are Equations (10) and (11) of Smallbone et al. with their link matrix replaced by the stoichiometric basis $B$; their Equation (12) is the scaling in item 2 written as $C^J=\operatorname{diag}(v)^{-1}C^{J\prime}\operatorname{diag}(v)$. Their perturbation is an additive change of one rate, which corresponds here to $e_{0,i}\,\partial/\partial e_i$ divided by $v^0_i$ when $v^0_i\ne0$. On the two-pool example with all constants $1$ every row of $C^{J\prime}$ is $(\tfrac13,\tfrac13,\tfrac13)$.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (8)–(12).
