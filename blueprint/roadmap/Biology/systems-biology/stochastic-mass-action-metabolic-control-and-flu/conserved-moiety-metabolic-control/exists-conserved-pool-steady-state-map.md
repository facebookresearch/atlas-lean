# Regular steady states with fixed conserved pools exist

An invertible reduced Jacobian gives a steady-state map through the chosen state, with fixed pool totals and a derivative at the base enzyme levels. This applies even when conservation makes the full Jacobian singular.

Let $M,R$ be finite with $R$ nonempty, $N\in\mathbb{R}^{M\times R}$ with $\operatorname{rank}N=q\ge1$ and a [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$, $N=BN_R$. Let $W\subseteq\mathbb{R}^M$ be open, $f_i\colon\mathbb{R}^M\to\mathbb{R}$ rate laws that are continuously differentiable on $W$, with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$, and let $e_0\in\mathbb{R}^R$, $s_0\in W$ satisfy

$$Nv(e_0,s_0)=0\qquad\text{and}\qquad J_{\mathrm{red}}:=N_R\,\varepsilon'(e_0,s_0)\,B\ \text{invertible},$$

with the [reduced Jacobian](conserved-pool-reduced-jacobian.md) of the network. Put $T=Ls_0$. Then there is a map $\sigma\colon\mathbb{R}^R\to\mathbb{R}^M$ such that:

1. $\sigma(e_0)=s_0$ and $\sigma$ is a [regular steady state with pool totals](conserved-pool-regular-steady-state.md) $T$ at $e_0$. In particular, $\sigma$ is differentiable at $e_0$, and on some open neighbourhood $U\ni e_0$ one has $\sigma(e)\in W$, $L\sigma(e)=T$ and $Nv(e,\sigma(e))=0$.
2. With $f(s_0)=(f_i(s_0))_{i\in R}$, its derivative is

$$D\sigma(e_0)=-B\,J_{\mathrm{red}}^{-1}N_R\operatorname{diag}\bigl(f(s_0)\bigr).$$

The regularity conclusion concerns differentiability at the base point $e_0$; it does not specify the other steady states in the pool class.

## Depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Reaction fluxes proportional to enzyme levels](../flux.md)

## Proof depends on

- [Existence of a regular steady-state map](../exists-is-regular-steady-state.md)
- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Control matrices of a network with conserved pools](conserved-pool-control-matrices.md)

## Expansion

Apply the [regular steady-state existence theorem](../exists-is-regular-steady-state.md) with metabolite space $\mathbb{R}^q$, stoichiometric matrix $N_R$, rate laws $\widetilde f_i(z)=f_i(s_0+Bz)$, enzyme levels $e_0$ and base state $z_0=0$. The rates are continuously differentiable at $0$. Since $B$ is injective, $Nv(e_0,s_0)=0$ implies $N_Rv(e_0,s_0)=0$. The regularity map in that theorem is

$$\delta\longmapsto N_R\operatorname{diag}(e_0)Df(s_0)B\delta=J_{\mathrm{red}}\delta,$$

which is injective by hypothesis. Thus there is a reduced steady-state map $\widetilde\sigma$ with $\widetilde\sigma(e_0)=0$, differentiable at $e_0$, and $N_Rv(e,s_0+B\widetilde\sigma(e))=0$ near $e_0$.

Set $\sigma(e)=s_0+B\widetilde\sigma(e)$. Then $\sigma(e_0)=s_0$, $L\sigma(e)=Ls_0+LB\widetilde\sigma(e)=T$, and multiplication by $B$ gives the full steady-state identity near $e_0$. Continuity at $e_0$ and openness of $W$ give a neighbourhood on which $\sigma(e)\in W$. Its reduced Jacobian at the base is $J_{\mathrm{red}}$, so it has all the stated regularity properties. Notice that the existence theorem is applied to the reduced network, not to the singular full Jacobian.

The derivative is the unscaled sensitivity identity in the [control-matrix calculation](conserved-pool-control-matrices.md). Differentiating the reduced steady-state equation gives

$$J_{\mathrm{red}}D\widetilde\sigma(e_0)=-N_R\operatorname{diag}(f(s_0)),$$

and multiplying by $B$ gives the displayed formula for $D\sigma(e_0)$, with no division by an enzyme level or a flux.

## Sources

- [Existence of a regular steady-state map](../exists-is-regular-steady-state.md), specialized to $(N_R,\widetilde f,e_0,0)$ as above. The fixed-pool conclusion is the affine lift by $B$; the derivative is the [control-matrix sensitivity identity](conserved-pool-control-matrices.md).
- Metabolic-control background: K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (7)–(12), for the reduced dynamics and first-order control matrices.
