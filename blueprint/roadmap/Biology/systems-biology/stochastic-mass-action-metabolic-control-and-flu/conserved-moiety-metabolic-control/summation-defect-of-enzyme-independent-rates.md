# Summation defect from enzyme-independent rates

When some reaction rates do not scale with an enzyme level (fixed inflows, dilution, nonenzymatic steps), the enzymatic control coefficients no longer sum to one; the defect is given exactly by the control matrix columns of the enzyme-independent reactions.

Let $M,R$ be finite, $N\in\mathbb{R}^{M\times R}$ with a [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$, $N=BN_R$, and split $R=R_e\sqcup R_0$. The rates are $v_i(e,s)=e_if_i(s)$ for $i\in R_e$ and $v_i(e,s)=g_i(s)$ for $i\in R_0$, with parameters $e\in\mathbb{R}^{R_e}$. Let $\sigma\colon\mathbb{R}^{R_e}\to\mathbb{R}^M$ satisfy the analogue, for these rates, of a [regular steady state with pool totals](conserved-pool-regular-steady-state.md) $T$ at $e_0$. Explicitly assume: $\sigma$ differentiable at $e_0$, all $f_i,g_i$ differentiable at $s_0=\sigma(e_0)$, $Nv(e,\sigma(e))=0$ and $L\sigma(e)=T$ near $e_0$, and $J_{\mathrm{red}}=N_R\varepsilon'B$ invertible, where $\varepsilon'_{im}=\partial v_i/\partial s_m$ at $(e_0,s_0)$ for all $i\in R$. Define $C^{s\prime}$ and $C^{J\prime}$ by the formulas of the [control matrices](conserved-pool-control-matrices.md), let $v^0=v(e_0,s_0)$ and $J(e)=v(e,\sigma(e))$. Then for every $m\in M$ and $j\in R$,

$$\sum_{i\in R_e}e_{0,i}\frac{\partial\sigma_m}{\partial e_i}(e_0)=-\sum_{i\in R_0}C^{s\prime}_{mi}v^0_i,\qquad \sum_{i\in R_e}e_{0,i}\frac{\partial J_j}{\partial e_i}(e_0)=v^0_j-\sum_{i\in R_0}C^{J\prime}_{ji}v^0_i .$$

In particular, for $v^0_j\ne0$ the scaled enzymatic flux control coefficients sum to $1-\sum_{i\in R_0}C^{J\prime}_{ji}v^0_i/v^0_j$, which is $1$ when $R_0=\varnothing$ and need not be $1$ otherwise. Example: a constant inflow $\varnothing\to S$ at rate $k_0>0$ and an outflow $S\to\varnothing$ at rate $e_1k_1s$ ($k_1>0$, $e_1>0$) have steady state $s=k_0/(e_1k_1)$ and flux $J_1=k_0$ independent of $e_1$, so $C^{J_1}_{e_1}=0$; the formula gives $1-C^{J\prime}_{10}v^0_0/v^0_1=1-1=0$.

## Depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Control matrices of a network with conserved pools](conserved-pool-control-matrices.md)

## Proof depends on

- [Control matrices of a network with conserved pools](conserved-pool-control-matrices.md)
- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)

## Expansion

The derivation of the control matrices goes through with $\partial v/\partial e_i=f_i(s_0)u_i$ for $i\in R_e$ (and no parameter for $R_0$): $e_{0,i}\,\partial\sigma/\partial e_i=C^{s\prime}u_iv^0_i$ and $e_{0,i}\,\partial J/\partial e_i=C^{J\prime}u_iv^0_i$ for $i\in R_e$. Summing over $R_e$ and using $C^{s\prime}v^0=0$ and $C^{J\prime}v^0=v^0$, which hold because $N_Rv^0=0$ for the full flux vector, gives the two identities. In the example $N=(1,-1)$, $B=(1)$, $N_R=(1,-1)$, $\varepsilon'=(0,e_1k_1)^{\mathsf T}$, $J_{\mathrm{red}}=-e_1k_1$ and $C^{J\prime}=\begin{pmatrix}1&0\\1&0\end{pmatrix}$.

The classical summation theorem rests on the fact that multiplying all enzyme levels by $\lambda$ multiplies every rate by $\lambda$, a rescaling of time that leaves concentrations unchanged and multiplies fluxes by $\lambda$. A rate that does not carry an enzyme factor breaks that rescaling, so the summation identity must be corrected as above; the same applies to growth-dilution terms written as $\mu s_m$ with a fixed growth rate $\mu$.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (8)–(11) (perturbation of a single rate and the resulting control matrices), from which the defect identity is derived here.
