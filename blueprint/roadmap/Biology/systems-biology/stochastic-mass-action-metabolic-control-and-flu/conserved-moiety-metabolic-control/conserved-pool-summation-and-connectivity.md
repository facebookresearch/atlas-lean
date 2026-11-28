# Summation and connectivity with conserved pools

With fixed conserved pools and every rate proportional to its enzyme level, the summation theorems keep their classical form, while connectivity holds only along directions of the stoichiometric subspace.

Let $\sigma$ be a [regular steady state with pool totals](conserved-pool-regular-steady-state.md) $T$ at $e_0$ for $N=BN_R$ with [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$ and rates $v_i(e,s)=e_if_i(s)$ for **every** $i\in R$. Let $s_0=\sigma(e_0)$, $v^0=v(e_0,s_0)$, $\varepsilon'=\varepsilon'(e_0,s_0)$, and let $C^{s\prime}$, $C^{J\prime}$ be the [control matrices](conserved-pool-control-matrices.md). Then:

1. **Concentration summation.** $C^{s\prime}v^0=0$; hence for every $m$ with $s_{0,m}>0$ the [concentration control coefficients](../conc-control.md) satisfy $\sum_{i\in R}C^{s_m}_{e_i}=0$.
2. **Flux summation.** $C^{J\prime}v^0=v^0$; hence for every $j$ with $v^0_j\ne0$ the [flux control coefficients](../flux-control.md) satisfy $\sum_{i\in R}C^{J_j}_{e_i}=1$.
3. **Connectivity on the stoichiometric subspace.** For every $\delta\in\operatorname{im}N$,

$$C^{J\prime}\varepsilon'\delta=0,\qquad C^{s\prime}\varepsilon'\delta=-\delta .$$

If moreover $v^0_i\ne0$ for all $i$ and $s_{0,m}>0$ for all $m$, then with the [elasticities](../elasticity.md) $\varepsilon^{v_i}_{s_m}$ at $(e_0,s_0)$, for every $\delta\in\operatorname{im}N$, every $j$ and every $m$,

$$\sum_{i\in R}C^{J_j}_{e_i}\sum_{m'\in M}\varepsilon^{v_i}_{s_{m'}}\frac{\delta_{m'}}{s_{0,m'}}=0,\qquad \sum_{i\in R}C^{s_m}_{e_i}\sum_{m'\in M}\varepsilon^{v_i}_{s_{m'}}\frac{\delta_{m'}}{s_{0,m'}}=-\frac{\delta_m}{s_{0,m}} .$$

4. **Metabolite-wise connectivity is conditional.** The classical identity $\sum_iC^{J_j}_{e_i}\varepsilon^{v_i}_{s_m}=0$ is the case $\delta=s_{0,m}u_m$ of item 3 and holds whenever the unit vector $u_m$ lies in $\operatorname{im}N$; it can fail otherwise. In the two-pool network $S_1+C_1\to S_2+C_2$, $S_2\to S_1$, $C_2\to C_1$ with all constants equal to $1$, $\sum_iC^{J_j}_{e_i}\varepsilon^{v_i}_{s_m}=\tfrac13$ for every $j$ and $m$.

Without conserved pools ($\operatorname{im}N=\mathbb{R}^M$) items 1–3 reduce to the [concentration summation](../sum-conc-control.md), [flux summation](../sum-flux-control.md) and [flux connectivity](../sum-flux-control-mul-elasticity.md) theorems. Items 1 and 2 use that the enzyme levels of **all** reactions are the parameters; with enzyme-independent rates see the [summation defect](summation-defect-of-enzyme-independent-rates.md).

## Depends on

- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Control matrices of a network with conserved pools](conserved-pool-control-matrices.md)
- [Concentration control coefficient](../conc-control.md)
- [Flux control coefficient](../flux-control.md)
- [Elasticity of a reaction rate](../elasticity.md)

## Proof depends on

- [Control matrices of a network with conserved pools](conserved-pool-control-matrices.md)
- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Elasticity of a reaction rate](../elasticity.md)

## Expansion

Since $Nv^0=0$ and $N=BN_R$ with $B$ injective, $N_Rv^0=0$, so $C^{s\prime}v^0=0$ and $C^{J\prime}v^0=v^0$; dividing the $m$-th, respectively $j$-th, entry by $s_{0,m}$, respectively $v^0_j$, and using item 2 of the control-matrix page gives items 1 and 2. For item 3 write $\delta=Bw$; then $\varepsilon'\delta=\varepsilon'Bw$ and $N_R\varepsilon'Bw=J_{\mathrm{red}}w$, so $C^{J\prime}\varepsilon'Bw=\varepsilon'Bw-\varepsilon'Bw=0$ and $C^{s\prime}\varepsilon'Bw=-Bw$. The scaled forms follow from $C^{J_j}_{e_i}=C^{J\prime}_{ji}v^0_i/v^0_j$, $C^{s_m}_{e_i}=C^{s\prime}_{mi}v^0_i/s_{0,m}$ and $\varepsilon^{v_i}_{s_{m'}}=s_{0,m'}\varepsilon'_{im'}/v^0_i$. For item 4 the example has $C^{J\prime}\varepsilon'$ with all entries $\tfrac13$, unit fluxes and unit concentrations, verified in exact rational arithmetic; there $u_m\notin\operatorname{im}N$ because $\operatorname{im}N=\ker L$ and $Lu_m\ne0$.

Smallbone et al. state that the summation and connectivity theorems follow from their Equations (10) and (11); item 4 records that, with conserved pools, the connectivity that follows is the one restricted to the stoichiometric subspace.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (10)–(13) and the sentence following them (“one may trivially deduce the summation and connectivity theorems”).
