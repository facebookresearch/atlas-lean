# Loop law for thermodynamically feasible fluxes

A flux admits chemical potentials making every active internal reaction strictly dissipative if and only if it has no sign-compatible internal cycle; the proof is a theorem of the alternative obtained from flux balance duality.

Let $M,R$ be finite, $S\in\mathbb{R}^{M\times R}$, and $R=I\sqcup E$ an internal/exchange split. For every flux $v\in\mathbb{R}^R$ the following are equivalent:

1. there is $\mu\in\mathbb{R}^M$ for which $v$ is [thermodynamically feasible](thermodynamically-feasible-flux.md), that is $v_r\Delta_rG(\mu)<0$ for every $r\in I$ with $v_r\ne0$;
2. $v$ is loopless: it has no [sign-compatible internal cycle](sign-compatible-internal-cycle.md).

No steady-state condition on $v$ is needed, and exchange reactions do not enter either side. When (1) holds, $\mu$ can be chosen with $v_r\Delta_rG(\mu)\le-|v_r|$ for every active internal $r$. The set of loopless fluxes is closed in $\mathbb{R}^R$.

## Depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Sign-compatible internal cycle of a flux](sign-compatible-internal-cycle.md)

## Proof depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Sign-compatible internal cycle of a flux](sign-compatible-internal-cycle.md)
- [Feasible fluxes of flux balance analysis](../fba-feasible.md)
- [Optimal value of flux balance analysis](../fba-value.md)
- [Feasible flux balance problem attains its optimum](../exists-fba-value-eq.md)
- [Strong duality for flux balance analysis](../exists-fba-dual-value-eq.md)
- [Dual feasibility for flux balance analysis](../fba-dual-feasible.md)
- [Dual objective of flux balance analysis](../fba-dual-value.md)

## Expansion

(1)$\Rightarrow$(2): if $k$ were a sign-compatible internal cycle, $\sum_{r\in I}k_r\Delta_rG(\mu)=\mu^{\mathsf T}Sk=0$, but each nonzero term equals $(k_r/v_r)\,v_r\Delta_rG(\mu)<0$.

(2)$\Rightarrow$(1): let $A=\{r\in I:v_r\ne0\}$; if $A=\varnothing$ any $\mu$ works. Otherwise identify $A$ with $\{1,\ldots,n\}$ and $M$ with $\{1,\ldots,m\}$ and let $\Omega'_{mr}=\operatorname{sign}(v_r)S_{mr}$ for $r\in A$. Consider the flux balance problem with matrix $\Omega'$, right-hand side $b=0$, bounds $l=0$, $u=\mathbf 1$ and objective $c=\mathbf 1$. It is [feasible](../fba-feasible.md) ($\kappa=0$), so it [attains its optimum](../exists-fba-value-eq.md) at some $\kappa^\ast$ with $V(0)=\sum_r\kappa^\ast_r\ge0$. If $V(0)>0$, then $k_r=\operatorname{sign}(v_r)\kappa^\ast_r$ on $A$ and $0$ elsewhere is a sign-compatible internal cycle, contradicting (2); so $V(0)=0$. [Strong duality](../exists-fba-dual-value-eq.md) gives a [dual feasible](../fba-dual-feasible.md) $(y,\alpha,\beta)$ with $\Omega'^{\mathsf T}y+\alpha-\beta=\mathbf 1$, $\alpha,\beta\ge0$, and [dual objective](../fba-dual-value.md) $0\cdot y+\mathbf 1\cdot\alpha-0\cdot\beta=0$, so $\alpha=0$ and $\Omega'^{\mathsf T}y=\mathbf 1+\beta\ge\mathbf 1$. With $\mu=-y$, for $r\in A$, $v_r\Delta_rG(\mu)=-|v_r|(\Omega'^{\mathsf T}y)_r\le-|v_r|$.

Closedness: if loopless $v^{(n)}\to v$ and $k$ were a sign-compatible internal cycle of $v$, then for large $n$ every $r$ with $k_r\ne0$ has $v^{(n)}_r$ of the sign of $v_r$, so $k$ would be one for $v^{(n)}$.

De Martino et al. state this alternative via Gordan's theorem for $\mu\Omega>0$ versus $\Omega k=0$, $k\ge0$, $k\ne0$; the argument above derives the same alternative from the box-bounded flux balance duality. The alternative concerns unrestricted potentials, not potentials constrained to measured concentration ranges.

## Sources

- D. De Martino, F. Capuani, M. Mori, A. De Martino and E. Marinari, Counting and correcting thermodynamically infeasible flux cycles in genome-scale metabolic networks, *Metabolites* 3 (2013), 946–966, [doi:10.3390/metabo3040946](https://doi.org/10.3390/metabo3040946): Section 1, Equations (2) and (3) and the appeal to Gordan's theorem of the alternatives between them; Section 2.2.2 (relaxation converges if and only if a solution of Equation (2) exists).
