# Loopless flux balance is not a linear program

When chemical potentials are free variables, the loopless flux balance problem still attains its optimum on a nonempty bounded feasible set, but its feasible set need not be convex, its optimal value need not be concave, and the linear-programming dual bound can be strict.

Let $S\in\mathbb{R}^{m\times n}$, $l,u,c\in\mathbb{R}^n$, $b\in\mathbb{R}^m$, and $I\subseteq\{1,\dots,n\}$ the internal reactions (the rest being exchange reactions). The **loopless feasible set** is

$$F_{\mathrm{th}}(b)=\{v\in\mathbb{R}^n:\ Sv=b,\ l\le v\le u,\ v\text{ is thermodynamically feasible for some }\mu\in\mathbb{R}^m\},$$

with feasibility as for [thermodynamically feasible fluxes](thermodynamically-feasible-flux.md), and $V_{\mathrm{th}}(b)=\max\{c\cdot v:v\in F_{\mathrm{th}}(b)\}$ when $F_{\mathrm{th}}(b)\ne\varnothing$. Then:

1. $F_{\mathrm{th}}(b)$ is compact, and if it is nonempty the maximum defining $V_{\mathrm{th}}(b)$ is attained.
2. $F_{\mathrm{th}}(b)$ need not be convex. For internal reactions $r_1\colon A\to B$, $r_2\colon B\to A$ and exchanges $x_A\colon\varnothing\to A$, $x_B\colon\varnothing\to B$, $b=0$ and bounds $[-1,1]$, the fluxes $(1,0,1,-1)$ and $(0,1,-1,1)$ lie in $F_{\mathrm{th}}(0)$ but their midpoint $(\tfrac12,\tfrac12,0,0)$ does not.
3. $V_{\mathrm{th}}$ need not be concave, and the linear-programming value can exceed it. For the internal pair $r_1,r_2$ alone, $S=\begin{pmatrix}-1&1\\1&-1\end{pmatrix}$, $b=(-t,t)$ with $t\in[-1,1]$, $0\le v\le1$ and $c=(1,1)$, the [optimal value](../fba-value.md) without the thermodynamic condition is $V(b)=2-|t|$, while $V_{\mathrm{th}}(b)=|t|$. Thus $V_{\mathrm{th}}(0)=0<\tfrac12V_{\mathrm{th}}(-1,1)+\tfrac12V_{\mathrm{th}}(1,-1)=1$, and at $b=0$ every [dual feasible](../fba-dual-feasible.md) point has [dual objective](../fba-dual-value.md) at least $2>V_{\mathrm{th}}(0)$.

Weak duality still bounds the loopless optimum: since $F_{\mathrm{th}}(b)\subseteq F(b)$, every LP dual feasible $(y,\alpha,\beta)$ satisfies

$$
V_{\mathrm{th}}(b)\le V(b)\le b\cdot y+u\cdot\alpha-l\cdot\beta
$$

whenever $F_{\mathrm{th}}(b)$ is nonempty. What need not transfer is equality with the dual bound or a linear shadow-price upper support. In item 3, such a support at $b=0$ would require $|t|\le t(y_2-y_1)$ for both $t=1$ and $t=-1$, which is impossible. With potentials fixed in advance the concavity and strong-duality results do apply, by [fixed-potential flux balance](fixed-potential-flux-balance-bounds.md).

## Depends on

- [Weak duality for flux balance analysis](../dot-product-le-fba-dual-value.md)
- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)
- [Optimal value of flux balance analysis](../fba-value.md)
- [Dual feasibility for flux balance analysis](../fba-dual-feasible.md)
- [Dual objective of flux balance analysis](../fba-dual-value.md)

## Proof depends on

- [Loop law for thermodynamically feasible fluxes](loopless-iff-exists-chemical-potential.md)
- [Sign-compatible internal cycle of a flux](sign-compatible-internal-cycle.md)
- [Weak duality for flux balance analysis](../dot-product-le-fba-dual-value.md)
- [Optimal value of flux balance analysis](../fba-value.md)

## Expansion

Item 1: by the [loop law](loopless-iff-exists-chemical-potential.md) $F_{\mathrm{th}}(b)$ is the intersection of the compact polytope $\{Sv=b,\ l\le v\le u\}$ with the closed set of loopless fluxes, and a continuous function attains its maximum on a nonempty compact set.

Item 2: both endpoints are steady; the first has $v_{r_1}>0=v_{r_2}$, feasible with $\mu_A>\mu_B$, the second $v_{r_2}>0=v_{r_1}$, feasible with $\mu_B>\mu_A$. At the midpoint both internal fluxes are positive, and $k=(1,1,0,0)$ is a [sign-compatible internal cycle](sign-compatible-internal-cycle.md), equivalently $\Delta_{r_1}G=-\Delta_{r_2}G$ cannot be negative for both.

Item 3: feasibility forces $v_1-v_2=t$. Without the thermodynamic condition the best choice is $v=(1,1-t)$ or $(1+t,1)$, giving $2-|t|$. Loopless fluxes cannot have $v_1,v_2>0$, so $v=(t,0)$ for $t\ge0$ and $(0,-t)$ for $t<0$, value $|t|$. Every dual objective bounds $V(b)=2$ at $t=0$ from above by [weak duality](../dot-product-le-fba-dual-value.md). Item 2 is adapted from the two-metabolite network of De Martino et al., with the $B$ exchange reversed and different flux bounds. They note that without thermodynamic constraints the steady flux states with bounds form a convex polytope and that their network carries an infeasible cycle when the two internal fluxes have the same sign. The values were rechecked on a grid of step $\tfrac1{100}$ in exact arithmetic.

## Sources

- D. De Martino, F. Capuani, M. Mori, A. De Martino and E. Marinari, Counting and correcting thermodynamically infeasible flux cycles in genome-scale metabolic networks, *Metabolites* 3 (2013), 946–966, [doi:10.3390/metabo3040946](https://doi.org/10.3390/metabo3040946): Section 1, Equation (1) and the following paragraph (convex polytope of steady states), Equations (2)–(3); Section 2.2.4, Figure 2 and Equations (8)–(11).
