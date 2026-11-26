# Global stability of mass-action futile cycles

**Network.** For $n \ge 1$ and $m_1, \dots, m_n \ge 1$, consider the mass-action futile cycle

$$P_{i-1} + E_i \rightleftharpoons C_{i1} \rightleftharpoons C_{i2} \rightleftharpoons \cdots \rightleftharpoons C_{i m_i} \longrightarrow P_i + E_i, \qquad i = 1, \dots, n,$$

with $P_n \equiv P_0$, forward rate constants $k_{ij} > 0$ ($j = 1, \dots, m_i + 1$) and reverse constants $k_{-ij} > 0$ ($j = 1, \dots, m_i$). The concentrations $x$ obey $\dot x = S\, r(x)$, where $S$ is the stoichiometric matrix and $r$ the vector of net reaction rates $r_{ij}$ in the forward direction. It includes processive multisite phosphorylation ($n = 2$, $m_1 = m_2 = m$). There are $n + 1$ conservation laws: total substrate $\sum_i [P_i] + \sum_{i,j} [C_{ij}] = \alpha$ and, for each chain, total enzyme $[E_i] + \sum_j [C_{ij}] = \beta_i$. A positive stoichiometric compatibility class is $\{x > 0 : x - x_0 \in \mathrm{im}(S)\}$.

**Lemma 1.** $\ker S = \mathrm{span}(\mathbf 1)$; hence at any equilibrium all net reaction rates $r_{ij}$ are equal.

**Theorem 6 (unique equilibrium).** For all $\alpha, \beta_i > 0$, every positive compatibility class contains exactly one equilibrium, and it is positive.

**Theorem 7 (global stability).** Every trajectory starting in a positive compatibility class converges to the unique equilibrium of that class.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Because the reaction graph is a single cycle of complexes, the only flux vectors balancing every species are the constant ones, which is Lemma 1. Equal rates make every equilibrium concentration a rational function of one unknown, say the last intermediate $c_{q m_q}$; substituting into the substrate conservation law gives a scalar equation on an admissible interval $(0, b_q)$, whose root exists by the intermediate value property and is unique by monotonicity arguments on the parametrization. For global stability, the piecewise linear in rates (PWLR) function

$$V(r) = \|r\|_\infty = \max_{i, j} |r_{ij}|$$

is nonincreasing along trajectories of the system written in the transformed variables of Equation (14): at a time when the maximum is attained by $|r_{ij}|$, its derivative is a nonnegative combination of differences $r_{kl} - r_{ij}$ of the opposite sign; LaSalle's invariance principle then shows that the largest invariant set in $\{\dot V = 0\}$ within a compatibility class is the equilibrium. This extends to longer chains the result previously obtained for processive phosphorylation with monotone systems theory, in contrast with distributive multisite phosphorylation, which can be multistationary.

## Sources

- S. Rao, "Global stability of a class of futile cycles", Journal of Mathematical Biology 74(3) (2017) 709, network (1), Equations (3), (9)-(10), (14), Lemma 1, Theorems 6-7, <https://doi.org/10.1007/s00285-016-1039-8>, PMCID PMC5258802.
