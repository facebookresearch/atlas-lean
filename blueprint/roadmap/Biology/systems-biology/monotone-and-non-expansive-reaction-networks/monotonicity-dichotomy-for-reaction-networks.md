# Monotonicity dichotomy for reaction networks

**Setting.** Let $\dot x = \Gamma R(x)$ be a reaction network under general kinetics, as in the [reaction-wise criterion](reaction-wise-criterion-for-monotonicity-and-non-expansivity.md). Its stoichiometric compatibility classes $(x + \operatorname{Im}\Gamma) \cap \mathbb{R}^n_{\ge 0}$ are forward invariant. The **R-graph** has one vertex per reaction and an arc $R_i \to R_j$ when a species involved in $R_i$ can change the rate of $R_j$.

**Statement.** Suppose the network (possibly lifted by appending species that appear in no reaction) has a strongly connected R-graph and is monotone, for every choice of general kinetics, with respect to a closed, pointed, convex cone $K$. Then exactly one of the following holds:

1. $K \cap \operatorname{Im}\Gamma = \{0\}$, and the network is non-expansive, for some norm, on each stoichiometric compatibility class;
2. $K \cap \operatorname{Im}\Gamma \ne \{0\}$, and the network is monotone with respect to the nontrivial cone $K' = K \cap \operatorname{Im}\Gamma$ lying inside the stoichiometric subspace.

Thus a search for kinetics-independent order structure can be split into a search for cones inside $\operatorname{Im}\Gamma$ and a search for norms on $\operatorname{Im}\Gamma$.

## Depends on

- [Reaction-wise criterion for monotonicity and non-expansivity](reaction-wise-criterion-for-monotonicity-and-non-expansivity.md)

## Expansion

If $x - y \in K'$ then $\phi_t(x) - \phi_t(y)$ lies in $K$ by monotonicity and in $\operatorname{Im}\Gamma$ because the difference of two points in one compatibility class stays in the stoichiometric subspace, which gives case 2. If $K$ meets $\operatorname{Im}\Gamma$ only at the origin, every affine slice $K \cap (x + \operatorname{Im}\Gamma)$ is bounded; a strongly connected R-graph lets one take a full-dimensional subset $C \subset K$ with $\operatorname{Im}\Gamma \subseteq \operatorname{Aff}(C - C)$, and the bounded convex slices of $K$ define a symmetric unit ball whose norm the flow does not increase, which gives case 1.

## Sources

- A. Duvall, Computationally checking if a reaction network is monotone or non-expansive, arXiv (2024). <https://doi.org/10.48550/arXiv.2409.12487> (Theorem 5, with Lemmas 6, 7, 8 and 10.)
