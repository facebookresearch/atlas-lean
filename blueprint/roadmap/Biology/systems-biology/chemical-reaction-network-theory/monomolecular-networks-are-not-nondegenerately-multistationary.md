# Monomolecular networks are not nondegenerately multistationary

Let $G$ be a reaction network with species $x \in \mathbb{R}^s_{\ge 0}$, stoichiometric subspace $S = \operatorname{span}\{y' - y : y \to y' \in G\}$, and mass-action vector field $f_\kappa$ for positive rate constants $\kappa$. Stoichiometric compatibility classes are $P = (x_0 + S) \cap \mathbb{R}^s_{\ge 0}$. A steady state $x^*$ is **nondegenerate** if $\operatorname{Im}\big(df_\kappa(x^*)|_S\big) = S$. $G$ is **multistationary** (respectively **nondegenerately multistationary**) if for some $\kappa > 0$ some class $P$ contains at least two positive (respectively nondegenerate positive) steady states.

**Proposition.** If every reactant complex of $G$ is either a single species with coefficient one or the zero complex, then $G$ is not nondegenerately multistationary.

The word "nondegenerately" cannot be dropped: for $G = \{0 \xleftarrow{\kappa_1} A \xrightarrow{\kappa_2} 2A\}$ the ODE is $\dot x_A = (\kappa_2 - \kappa_1) x_A$, so if $\kappa_1 = \kappa_2$ every positive $x_A$ is a degenerate steady state, and otherwise there is none. Multistationarity is also not inherited by enlarging a network: $\{0 \rightleftharpoons A,\ 2A \rightleftharpoons 3A\}$ is multistable, but adding $A \to B$ produces a network with no positive steady state for any rate constants, because $x_B$ grows without bound.

## Expansion

With at-most-monomolecular reactants each component of $f_\kappa$ is affine in $x$: $f_\kappa(x) = Mx + b$ with a constant matrix $M = df_\kappa(x)$, and $Mv \in S$ for every $v$ because $f_\kappa$ takes values in $S$. The steady states in $P$ are therefore the points of the nonnegative orthant that solve the linear system $Mx + b = 0$, $\langle x - x_0, v \rangle = 0$ for $v$ in a basis of $S^\perp$: the intersection of an affine solution set with $\mathbb{R}^s_{\ge 0}$, which need not itself be affine (for $0 \leftarrow A \rightarrow 2A$ with equal rates it is $[0,\infty)$). If $x^* \ne x^{**}$ are two positive steady states in $P$, then $x^* - x^{**}$ is a nonzero vector of $S$ with $M(x^* - x^{**}) = 0$, so $M|_S : S \to S$ has a nontrivial kernel and is not onto $S$. Since $M$ does not depend on the point, every steady state in $P$ is then degenerate. Hence $P$ contains at most one nondegenerate positive steady state. The counterexample to lifting shows that results transferring multistationarity from a subnetwork to the full network need extra hypotheses, for instance that both networks contain all inflow and outflow reactions (Joshi–Shiu).

## Sources

- E. Gross, H. Harrington, N. Meshkat and A. Shiu, "Joining and decomposing reaction networks", Journal of Mathematical Biology (2020), Section 5 (Definitions 5.1–5.2, Proposition 5.3, Remark 5.4, Example 5.5), <https://doi.org/10.1007/s00285-020-01477-y>.
