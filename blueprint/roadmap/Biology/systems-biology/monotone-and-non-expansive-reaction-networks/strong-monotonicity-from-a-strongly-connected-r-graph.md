# Strong monotonicity and weak contractivity from a strongly connected R-graph

**Setting.** Let $\dot x = \Gamma R(x)$ be a reaction network under general kinetics with flow $\phi_t$, as in the [reaction-wise criterion](reaction-wise-criterion-for-monotonicity-and-non-expansivity.md). The system is **strongly monotone** with respect to a cone $K$ if $x \le_K y$, $x \ne y$ implies $\phi_t(y) - \phi_t(x) \in \operatorname{int} K$ (interior relative to the stoichiometric subspace) for $t > 0$; it is **weakly contractive** for a norm if $|\phi_t(x) - \phi_t(y)| < |x - y|$ for all $x \ne y$ in one compatibility class and $t > 0$.

**Statement.** Suppose the R-graph of the network is strongly connected.

1. If the network is monotone with respect to a cone $K \subseteq \operatorname{Im}\Gamma$, it is strongly monotone with respect to $K$.
2. If it is non-expansive for some norm, it is weakly contractive for that norm. In particular, a network non-expansive for a polyhedral norm with strongly connected R-graph is weakly contractive.
3. A weakly contractive network is concordant: $\Gamma R$ is injective on every stoichiometric compatibility class for every choice of general kinetics, so each class contains at most one equilibrium.

## Depends on

- [Reaction-wise criterion for monotonicity and non-expansivity](reaction-wise-criterion-for-monotonicity-and-non-expansivity.md)

## Expansion

Strong monotonicity follows from Hirsch's criterion: besides the boundary inequality $k_2^\top J k_1 \ge 0$, each boundary vector $k_1$ must admit a supporting functional $k_2$ with strict inequality somewhere along the trajectory. Strong connectivity of the R-graph propagates a perturbation of any one reaction rate to every other reaction, which supplies the strict inequality for each face of $K$; the same propagation along faces of the unit ball turns non-expansivity into weak contractivity. Two distinct equilibria in one class would have constant distance under the flow, contradicting weak contractivity, which gives concordance.

## Sources

- A. Duvall, Computationally checking if a reaction network is monotone or non-expansive, arXiv (2024). <https://doi.org/10.48550/arXiv.2409.12487> (Theorem 4, Corollary 3, Lemma 16; background Theorem 3.)
