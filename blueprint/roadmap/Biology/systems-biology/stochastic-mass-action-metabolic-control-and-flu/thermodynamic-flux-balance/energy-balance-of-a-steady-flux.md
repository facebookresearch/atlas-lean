# Energy balance of a steady flux

At a steady flux the free energy dissipated by internal reactions equals the free energy supplied through exchange reactions; a closed steady network therefore cannot carry a nonzero flux in which every active reaction strictly dissipates.

Let $M,R$ be finite, $S\in\mathbb{R}^{M\times R}$, $R=I\sqcup E$ an internal/exchange split, $\mu\in\mathbb{R}^M$, and let $\Delta_rG(\mu)=(S^{\mathsf T}\mu)_r$ as for [thermodynamically feasible fluxes](thermodynamically-feasible-flux.md). For every $v\in\mathbb{R}^R$ with $Sv=0$,

$$\sum_{r\in I}v_r\,\Delta_rG(\mu)=-\sum_{x\in E}v_x\,(S^{\mathsf T}\mu)_x .$$

Consequences, for $v$ with $Sv=0$. The exchange term uses the same modelled-species potentials $\mu$ as the internal term; separate reservoir-side potentials and interfacial dissipation are not modelled here:

1. **Exchanges power dissipation.** If $v$ is thermodynamically feasible for $\mu$ and some internal reaction is active, then $\sum_{x\in E}v_x(S^{\mathsf T}\mu)_x>0$.
2. **Closed networks.** If $E=\varnothing$, or more generally $v_x=0$ for all $x\in E$, and $v$ is thermodynamically feasible for some $\mu$, then $v_r=0$ for every $r\in I$. In particular, requiring strict dissipation $v_r\Delta_rG(\mu)<0$ of every reaction of a closed network leaves no nonzero steady flux.
3. **Cycles carry no net driving force.** Every [sign-compatible internal cycle](sign-compatible-internal-cycle.md) $k$ satisfies $\sum_{r\in I}k_r\Delta_rG(\mu)=0$ for every $\mu$, so a flux with such a cycle cannot be feasible for any $\mu$.

Witnesses: the closed cycle $A\to B\to C\to A$ with unit fluxes has $\sum_r\Delta_rG(\mu)=0$ for every $\mu$ and is never feasible. The open pathway with uptake $\varnothing\to A$, internal $A\to B$ and secretion $B\to\varnothing$, all with unit flux, is steady and feasible for $\mu_A=1$, $\mu_B=0$; the internal term is $-1$ and the uptake supplies $\mu_A=1$. The abstract co-substrate cycle $A\to B$, $B\to C$, $C+X\to A+Y$ with $X$ supplied and $Y$ removed by exchanges is feasible for the synthetic potentials $\mu=(0,-1,-2,10,0)$ in the order $A,B,C,X,Y$, while its reverse is infeasible whenever $\mu_X>\mu_Y$. This toy model specifies no chemical formulas or ATP-hydrolysis mechanism.

## Depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Sign-compatible internal cycle of a flux](sign-compatible-internal-cycle.md)

## Proof depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Sign-compatible internal cycle of a flux](sign-compatible-internal-cycle.md)

## Expansion

The identity is $0=\mu^{\mathsf T}Sv=\sum_{r\in R}v_r(S^{\mathsf T}\mu)_r$, split over $I$ and $E$. Item 1: every term of the left side is negative or zero and at least one is negative. Item 2: the right side is $0$, while the left side is negative as soon as one internal reaction is active. Item 3: $\sum_rk_r\Delta_rG(\mu)=\mu^{\mathsf T}Sk=0$, while feasibility would make each term $k_r\Delta_rG(\mu)=(k_r/v_r)\,v_r\Delta_rG(\mu)$ with $k_r\ne0$ negative. For the reversed co-substrate cycle, adding the three internal Gibbs energies gives $\mu_X-\mu_Y$ for the reversed directions, which must be negative for feasibility.

Kümmel et al. state that internal cycles with no net conversion have zero overall driving force and are infeasible, attributing the constraint to Beard, Liang and Qian (Biophysical Journal 83, 2002), and illustrate that the same cycle becomes feasible when coupled to the conversion of a high-energy co-substrate, while its reverse would act as an energy generator.

## Sources

- A. Kümmel, S. Panke and M. Heinemann, Systematic assignment of thermodynamic constraints in metabolic network models, *BMC Bioinformatics* 7 (2006), article 512, [doi:10.1186/1471-2105-7-512](https://doi.org/10.1186/1471-2105-7-512): Background (internal reaction cycles without net conversion have zero overall driving force, reference 19), Results, Equation (1), and “Identification of thermodynamically infeasible operation of reaction sets” with Figure 2 (co-substrate-driven cycle).
