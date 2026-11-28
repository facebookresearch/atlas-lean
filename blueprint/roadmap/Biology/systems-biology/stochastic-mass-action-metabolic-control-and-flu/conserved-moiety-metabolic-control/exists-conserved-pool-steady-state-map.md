# Steady-state maps with fixed conserved pools exist by the implicit function theorem

If the reduced Jacobian is invertible at a steady state, the steady state continues uniquely, within its class of fixed pool totals, to a continuously differentiable map of the enzyme levels, even though the full Jacobian is singular.

Let $M,R$ be finite with $R$ nonempty, $N\in\mathbb{R}^{M\times R}$ with $\operatorname{rank}N=q\ge1$ and a [conserved-pool presentation](conserved-pool-reduced-coordinates.md) $(B,L)$, $N=BN_R$. Let $W\subseteq\mathbb{R}^M$ be open, $f_i\colon\mathbb{R}^M\to\mathbb{R}$ rate laws that are continuously differentiable on $W$, with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$, and let $e_0\in\mathbb{R}^R$, $s_0\in W$ satisfy

$$Nv(e_0,s_0)=0\qquad\text{and}\qquad J_{\mathrm{red}}:=N_R\,\varepsilon'(e_0,s_0)\,B\ \text{invertible},$$

with the [reduced Jacobian](conserved-pool-reduced-jacobian.md) of the network. Put $T=Ls_0$. Then there are open sets $U\ni e_0$ in $\mathbb{R}^R$ and $V\ni0$ in $\mathbb{R}^q$ with $s_0+BV\subseteq W$, and a unique map $\zeta\colon U\to V$, such that for all $(e,z)\in U\times V$

$$Nv(e,s_0+Bz)=0\iff z=\zeta(e).$$

Moreover $\zeta$ is continuously differentiable with $\zeta(e_0)=0$, and the lifted map $\sigma(e)=s_0+B\zeta(e)$ on $U$ (extended by $\sigma(e)=s_0$ off $U$) satisfies:

1. $\sigma(e_0)=s_0$, $L\sigma(e)=T$ and $Nv(e,\sigma(e))=0$ for $e\in U$, and $\sigma$ is a [regular steady state with pool totals](conserved-pool-regular-steady-state.md) $T$ at $e_0$;
2. **local uniqueness in the class:** every steady state $s\in s_0+BV$ at enzyme levels $e\in U$ with $Ls=T$ equals $\sigma(e)$;
3. **derivative:** with $f(s_0)=(f_i(s_0))_{i\in R}$,

$$D\sigma(e_0)=-B\,J_{\mathrm{red}}^{-1}N_R\operatorname{diag}\bigl(f(s_0)\bigr).$$

Steady states with other pool totals are not described by $\sigma$; uniqueness holds only inside the class $Ls=T$.

## Depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)
- [Reaction fluxes proportional to enzyme levels](../flux.md)

## Proof depends on

- [Implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)
- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reduced Jacobian of a conserved-pool network](conserved-pool-reduced-jacobian.md)
- [Regular steady state with fixed conserved pools](conserved-pool-regular-steady-state.md)

## Expansion

Define $F(e,z)=N_R\,v(e,s_0+Bz)$ on the open set $\{(e,z):s_0+Bz\in W\}\subseteq\mathbb{R}^R\times\mathbb{R}^q$; it is $C^1$ because each $v_i$ is a product of a coordinate of $e$ and a $C^1$ function of $z$. By the reduced-coordinate page, $Nv=0$ if and only if $N_Rv=0$, so the zero sets of $F$ and of $(e,z)\mapsto Nv(e,s_0+Bz)$ agree, and $F(e_0,0)=0$. Its partial derivatives at $(e_0,0)$ are $D_zF=N_R\operatorname{diag}(e_0)Df(s_0)B=J_{\mathrm{red}}$ and $D_eF=N_R\operatorname{diag}(f(s_0))$. The [implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md) with $n=|R|\ge1$, $m=q\ge1$, $k=1$ gives $U$, $V$, $\zeta$, the equivalence, and $D\zeta(e_0)=-J_{\mathrm{red}}^{-1}N_R\operatorname{diag}(f(s_0))$. Then $L\sigma=Ls_0+LB\zeta=T$, the steady-state identity holds on $U$, $\sigma$ is differentiable at $e_0$, $f$ is differentiable at $s_0$, and the reduced Jacobian at $(e_0,\sigma(e_0))$ is $J_{\mathrm{red}}$; this is item 1. Item 2: a steady state $s$ with $Ls=T$ lies in $s_0+\operatorname{im}B$, so $s=s_0+Bz$ with a unique $z$, and $z\in V$ gives $z=\zeta(e)$. Item 3 is $D\sigma(e_0)=B\,D\zeta(e_0)$.

On the two-pool example $S_1+C_1\to S_2+C_2$, $S_2\to S_1$, $C_2\to C_1$ (all constants $1$) a central finite-difference check of $\sigma$, computed by Newton iteration inside the class, agrees with the derivative formula to $10^{-6}$. The full-state theorem for [regular steady states](../exists-is-regular-steady-state.md) is the case without conserved pools.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (7)–(9) (linearized reduced dynamics and the new steady state $x=-\delta L(N_r\varepsilon'L)^{-1}N_{r,j}$ after perturbing reaction $j$), of which item 3 is the nonlinear, enzyme-parametrized counterpart.
