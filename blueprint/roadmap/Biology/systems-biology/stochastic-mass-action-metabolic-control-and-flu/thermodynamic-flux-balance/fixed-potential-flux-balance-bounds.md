# Flux balance with fixed chemical potentials is a bounded linear program

With chemical potentials fixed in advance, thermodynamic feasibility only tightens flux bounds, so the thermodynamically constrained problem is an ordinary flux balance problem and inherits attainment, duality and concavity.

Let $S\in\mathbb{R}^{m\times n}$, flux bounds $l,u\in\mathbb{R}^n$, objective $c\in\mathbb{R}^n$, right-hand side $b\in\mathbb{R}^m$, a set $I\subseteq\{1,\dots,n\}$ of internal reactions, and chemical potentials $\mu\in\mathbb{R}^m$ with $\Delta_rG(\mu)=(S^{\mathsf T}\mu)_r$. Define tightened bounds $l',u'$ by $l'_r=l_r$, $u'_r=u_r$ for $r\notin I$ and, for $r\in I$,

$$(l'_r,u'_r)=\begin{cases}(\max(l_r,0),\,u_r)&\Delta_rG(\mu)<0,\\ (l_r,\,\min(u_r,0))&\Delta_rG(\mu)>0,\\ (\max(l_r,0),\,\min(u_r,0))&\Delta_rG(\mu)=0.\end{cases}$$

Then the set of [feasible fluxes](../fba-feasible.md) $v$ ($Sv=b$, $l\le v\le u$) that are [thermodynamically feasible for $\mu$](thermodynamically-feasible-flux.md) is exactly the feasible set $F'(b)=\{v:Sv=b,\ l'\le v\le u'\}$. Consequently, whenever $F'(b)$ is nonempty, the maximum of $c\cdot v$ over it is attained and equals the [optimal value](../fba-value.md) $V'(b)$ for the bounds $l',u'$; strong duality holds with [dual feasible](../fba-dual-feasible.md) points and the [dual objective](../fba-dual-value.md) for $l',u'$; and $V'$ is concave on the set of right-hand sides with nonempty $F'(b)$. $F'(b)$ is empty whenever $l'_r>u'_r$ for some $r$, for instance when $l_r>0$ forces an internal reaction against its Gibbs energy.

## Depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Feasible fluxes of flux balance analysis](../fba-feasible.md)
- [Optimal value of flux balance analysis](../fba-value.md)
- [Dual feasibility for flux balance analysis](../fba-dual-feasible.md)
- [Dual objective of flux balance analysis](../fba-dual-value.md)

## Proof depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Feasible fluxes of flux balance analysis](../fba-feasible.md)
- [Feasible flux balance problem attains its optimum](../exists-fba-value-eq.md)
- [Strong duality for flux balance analysis](../exists-fba-dual-value-eq.md)
- [Concavity of the flux balance optimum in the right-hand side](../fba-value-concave.md)

## Expansion

By the equivalent form of feasibility for $\mu$, an internal $v_r$ must be $\ge0$, $\le0$ or $=0$ according as $\Delta_rG(\mu)$ is negative, positive or zero, and nothing is required of other reactions; intersecting with $l\le v\le u$ gives exactly $l'\le v\le u'$. The three consequences are the [attainment](../exists-fba-value-eq.md), [strong duality](../exists-fba-dual-value-eq.md) and [concavity](../fba-value-concave.md) theorems applied to the data $(S,l',u',c)$.

This is the mathematical content of assigning reaction directions from the sign of the reaction Gibbs energy, as in the thermodynamic facts-based step of Kümmel et al., where an internal reaction whose Gibbs energy range is entirely negative (positive) is made irreversible forward (backward). When the potentials are not fixed but chosen together with the flux, the constraint is no longer a box and these conclusions can fail: see [loopless flux balance](loopless-flux-balance-is-not-convex.md). With fixed potentials on a closed network at $b=0$ the feasible set reduces to $v_I=0$ by the [energy balance](energy-balance-of-a-steady-flux.md).

## Sources

- A. Kümmel, S. Panke and M. Heinemann, Systematic assignment of thermodynamic constraints in metabolic network models, *BMC Bioinformatics* 7 (2006), article 512, [doi:10.1186/1471-2105-7-512](https://doi.org/10.1186/1471-2105-7-512): Results, Equation (1) and “Thermodynamic facts-based assignment”, with Figure 1b (if the maximal reaction Gibbs energy is negative the reaction is irreversible forward; if the minimal one is positive, irreversible backward).
