# Regular steady state with fixed conserved pools

A regular steady state with fixed conserved pools is a steady-state map that keeps every pool total fixed and whose reduced Jacobian is invertible, replacing the full-state regularity condition that conserved pools rule out.

Let $M,R$ be finite, $N\in\mathbb{R}^{M\times R}$ with a [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$, $N=BN_R$, let $f_i\colon\mathbb{R}^M\to\mathbb{R}$, $i\in R$, be rate laws with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$, let $e_0\in\mathbb{R}^R$ and $T\in\mathbb{R}^p$. A map $\sigma\colon\mathbb{R}^R\to\mathbb{R}^M$ is a **regular steady state with pool totals $T$ at $e_0$** when

- $\sigma$ is differentiable at $e_0$ and every $f_i$ is differentiable at $\sigma(e_0)$;
- there is a neighbourhood $U$ of $e_0$ with $Nv(e,\sigma(e))=0$ and $L\sigma(e)=T$ for all $e\in U$;
- the [reduced Jacobian](conserved-pool-reduced-jacobian.md) $J_{\mathrm{red}}(e_0,\sigma(e_0))=N_R\,\varepsilon'(e_0,\sigma(e_0))\,B$ is invertible.

The definition does not depend on the choice of $(B,L)$: changing $L$ to $QL$ changes $T$ to $QT$, and invertibility of the reduced Jacobian is choice independent. When $\operatorname{rank}N=|M|$ (no conserved pool, $p=0$), the pool condition is empty and, since $N\varepsilon'=B\,J_{\mathrm{red}}B^{-1}$, the definition coincides with the full-state [regular steady state](../is-regular-steady-state.md).

## Depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Reaction fluxes proportional to enzyme levels](../flux.md)

## Proof depends on

- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)

## Expansion

Choice independence is item 1 of the [reduced Jacobian](conserved-pool-reduced-jacobian.md) page together with item 4 of the [reduced coordinates](conserved-pool-reduced-coordinates.md) page. For $p=0$, $B$ is invertible and $N\varepsilon'=BN_R\varepsilon'BB^{-1}=BJ_{\mathrm{red}}B^{-1}$, so injectivity of $N\varepsilon'$ is invertibility of $J_{\mathrm{red}}$. Existence of such maps is the [conserved-pool implicit function theorem](exists-conserved-pool-steady-state-map.md).

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (7)–(9) (reduced dynamics assuming an invertible $N_r\varepsilon'L$ and the perturbed steady state).
