# Second-order cone representation of Michaelis–Menten flux bounds

**Kinetic flux bound.** In a metabolic network with stoichiometric matrix $S$, fluxes $v$ and metabolite concentrations $z \ge 0$, let each reaction $i$ in a set $Q$ be limited by Michaelis–Menten kinetics in its substrate $z_{\sigma(i)}$ with maximal rate $V_i^{\max} > 0$ and Michaelis constant $K_i^m > 0$:

$$0 \le v_i \le \frac{V_i^{\max} z_{\sigma(i)}}{K_i^m + z_{\sigma(i)}} \qquad \text{(Equation 2)}.$$

**SOC representation.** Writing $V = V_i^{\max}$, $K = K_i^m$, $z = z_{\sigma(i)}$, for $z \ge 0$ and $v \ge 0$ the bound is equivalent to the hyperbolic constraint $VK \le (V - v)(K + z)$ with $V - v \ge 0$, i.e. to the second-order cone constraint

$$\left\| \begin{pmatrix} 2\sqrt{VK} \\ (V - v) - (K + z) \end{pmatrix} \right\|_2 \le (V - v) + (K + z),$$

which the paper writes in an equivalent rescaled form (Equation 4). The set of feasible $(v, z)$ is therefore convex, although the rate law is nonlinear.

**Conic flux balance analysis (CFBA).** Maximizing a linear objective $c^\top v$ subject to $Sv = 0$, linear flux and concentration bounds, and the cone constraints above for $i \in Q$ is a second-order cone program; it predicts steady-state fluxes and concentrations together, and conic duality yields sensitivities of the optimum to $V_i^{\max}$ and $K_i^m$.

**Several substrates.** If reaction $i$ has $p_i$ substrates with individual bounds $v_{ik} \le V_{ik}^{\max} z_{\sigma_k(i)}/(K_{ik}^m + z_{\sigma_k(i)})$, the product bound $v_i \le \prod_k v_{ik}$ is nonconvex; the weighted geometric-mean surrogate $v_i \le \prod_k v_{ik}^{\pi_{ik}}$ with $\sum_k \pi_{ik} \le 1$ is SOC representable (Equation 5), and for $p_i = 2$, $\pi_{i1} = \pi_{i2} = \tfrac12$ it is $\big\|(2 v_i,\ v_{i1} - v_{i2})\big\|_2 \le v_{i1} + v_{i2}$ (Equation 6).

## Depends on

- [Michaelis constant](../../michaelis-menten-kinetics-and-the-quasi-steady-s/michaelis-constant.md)

## Expansion

Expanding $(V - v)(K + z) \ge VK$ gives $Vz \ge v(K + z)$, the Michaelis–Menten inequality, and the standard identity $x_1^2 \le x_2 x_3,\ x_2, x_3 \ge 0 \iff \|(2x_1, x_2 - x_3)\| \le x_2 + x_3$ turns it into a cone constraint. Convexity reflects that $z \mapsto Vz/(K+z)$ is concave, so its hypograph is convex. Linear FBA cannot predict concentrations because fluxes are its only variables; CFBA keeps tractability while coupling fluxes to concentrations, and dynamic FBA and minimal cut set analysis carry over: cut sets of networks with reactions and metabolites correspond to irreducible infeasible subsystems of a conic system, found as extreme points of an alternative system via results on infeasibility of semidefinite systems.

## Sources

- J. A. Taylor, A. Rapaport, D. Dochain, "Convex representation of metabolic networks with Michaelis–Menten kinetics", Bulletin of Mathematical Biology 86 (2024) 65, Equations (2)–(6), Sections 2–4, <https://doi.org/10.1007/s11538-024-01293-1> (PMC11052807).
