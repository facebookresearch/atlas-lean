# Sign-nonsingularity criterion for injectivity of reaction networks under monotone kinetics

**Setting.** As for power-law kinetics, let $A \in \mathbb{R}^{n\times m}$ (rank $s$) be the stoichiometric matrix of a network with dynamics $\dot{c} = AK(c)$, and let $\tilde{M}$ denote the matrix obtained from an $n\times n$ matrix $M$ by replacing its first $d = n - s$ rows with a reduced basis of $\operatorname{im}(A)^\perp$.

**Influence specifications.** An influence specification is an $m\times n$ sign matrix $Z = (z_{j,i}) \in \{+,-,0\}^{m\times n}$ recording whether species $i$ increases, decreases or does not affect the rate of reaction $j$. A kinetics $K$ is strictly monotonic with respect to $Z$ if $K_j(c) > 0$ exactly when all species in $z_j^+ = \{i : z_{j,i} = +\}$ are present, and on that set $K_j$ is strictly increasing in $c_i$ for $z_{j,i} = +$, strictly decreasing for $z_{j,i} = -$ and constant for $z_{j,i} = 0$. Write $\mathcal{K}(Z)$ for these kinetics, $\mathcal{K}^d(Z)$ for those differentiable with partial derivatives of constant sign $z_{j,i}$, and $\mathcal{K}^g(Z)$ for the power-law kinetics whose kinetic order $V$ has $\operatorname{sign}(V) = Z$. Hill-type, Michaelis–Menten and Lotka–Volterra rates are typical members of $\mathcal{K}(Z)$.

**A-sign-nonsingularity.** Let $\Sigma(Z) = \{V \in \mathbb{R}^{m\times n} : \operatorname{sign}(V) = Z\}$. $Z$ is $A$-sign-nonsingular (A-SNS) if $V \mapsto \operatorname{sign}\det(\widetilde{AV})$ is constant and nonzero on $\Sigma(Z)$. Equivalently, with a symbolic matrix $X$ and $Z_X = Z * X$ (entrywise sign times symbol), the polynomial

$$p_Z(X) = \det(\widetilde{AZ_X}) = \sum_{|I| = |J| = s}\det(A_{I,J})\det\big((Z_X)_{J,I}\big)$$

is nonzero and all its monomials have coefficients of one sign.

**Theorem.** The following are equivalent:

1. $A$ is $Z$-injective over all strictly monotonic kinetics $\mathcal{K}(Z)$, i.e. $AK(a) \ne AK(b)$ for every $K \in \mathcal{K}(Z)$ and every pair of distinct stoichiometrically compatible concentration vectors that are non-overlapping with respect to $Z$;
2. $A$ is $Z$-injective over $\mathcal{K}^d(Z)$;
3. $A$ is injective over the power-law kinetics $\mathcal{K}^g(Z)$;
4. $Z$ is A-SNS.

Consequently, if $Z$ is A-SNS the network cannot have two distinct positive steady states in one stoichiometric class for any rates in $\mathcal{K}(Z)$, independently of their functional form, nor, for kinetics in $\mathcal{K}^d(Z)$, a degenerate positive steady state.

## Depends on

- [Determinant criterion for injectivity of reaction networks under power-law kinetics](determinant-criterion-for-injectivity-under-power-law-kinetics.md)

## Expansion

Power-law kinetics are dense among monotone kinetics in the sense relevant here: the Jacobian of any $K \in \mathcal{K}^d(Z)$ at a point has the sign pattern $Z$, and so does the Jacobian of some power-law kinetics with the same values and derivatives at that point. Hence the determinant condition for all monotone kinetics reduces to the power-law determinant criterion over all $V$ with sign pattern $Z$, which is exactly sign-nonsingularity of the polynomial $p_Z$. Checking A-SNS requires one symbolic determinant and inspection of its coefficient signs, and it unifies earlier injectivity tests for mass-action, non-catalytic and weakly monotonic kinetics as well as interaction-graph criteria for gene regulatory networks.

## Sources

- Carsten Wiuf and Elisenda Feliu, "Power-Law Kinetics and Determinant Criteria for the Preclusion of Multistationarity in Networks of Interacting Species", SIAM Journal on Applied Dynamical Systems 12 (2013), 1685–1721, <https://doi.org/10.1137/120873388>; numbering as in arXiv:1202.3621: Section 9 (influence specifications, A-sign-nonsingularity and the propositions and corollaries relating injectivity over power-law kinetics to A-SNS) and Section 10 (Theorems 10.1 and 10.2 and Corollary 10.3).
