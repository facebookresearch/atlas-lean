# Sign criterion for multistationarity of networks with toric steady states

**Setting.** Consider a mass-action reaction network $G$ with $s$ species, $m$ complexes and $r$ reactions, stoichiometric matrix $N$ and steady-state equations $\dot x = \Sigma\,\Psi(x)$. Assume that a partition $I_1,\dots,I_d$ of the complexes satisfies, for every choice of rate constants, condition (C1) of the binomial steady-state theorem (a basis of $\ker\Sigma$ with supports $I_1,\dots,I_d$), so that positive steady states, when they exist, are the monomially parametrized set $\tilde x \cdot t^{A}$, where $A \in \mathbb{Z}^{w \times s}$ has kernel spanned by the differences $y_{j_2} - y_{j_1}$ within blocks. Let $Z \in \mathbb{Z}^{s \times q}$ be an integer matrix (typically with $\ker Z^t$ equal to the stoichiometric subspace). The network is *multistationary with respect to $\ker Z^t$* for a rate vector if there are two distinct positive steady states $x^1 \neq x^2$ with $x^1 - x^2 \in \ker Z^t$.

**Theorem.** Assume in addition that the flux cone $\ker N \cap \mathbb{R}^r_{\ge 0}$ is not contained in any coordinate hyperplane. Then some rate constant vector makes $G$ multistationary with respect to $\ker Z^t$ if and only if there is an orthant of $\mathbb{R}^s$ that both $\operatorname{im}(A^t)$ and $\ker(Z^t)$ meet nontrivially, i.e. there exist nonzero $\alpha \in \operatorname{im}(A^t)$ and $\sigma \in \ker(Z^t)$ with $\operatorname{sign}(\alpha) = \operatorname{sign}(\sigma)$.

Given such $\alpha, \sigma$, explicit witnesses are

$$x^1_i = \frac{\sigma_i}{e^{\alpha_i} - 1}\ (\alpha_i \neq 0), \qquad x^2 = x^1 \cdot e^{\alpha} \ (\text{coordinatewise}),$$

with arbitrary positive $x^1_i = x^2_i$ where $\alpha_i = 0$, and a rate vector $k = \operatorname{diag}(\phi(x^1))^{-1} M \lambda$ obtained from a generator matrix $M$ of the flux cone, where $\phi(x)$ is the vector of reactant monomials.

## Depends on

- [Binomial steady-state ideals and monomial parametrization of positive steady states](binomial-steady-state-ideals-and-toric-parametrization.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

Two positive steady states on the same toric variety differ by $\ln x^2 - \ln x^1 = \alpha \in \operatorname{im}(A^t)$, and they are stoichiometrically compatible iff $\sigma = x^2 - x^1 \in \ker Z^t$. Since $x^2_i - x^1_i = x^1_i(e^{\alpha_i} - 1)$ has the sign of $\alpha_i$, the two vectors must share a sign pattern; conversely, any sign-compatible pair can be solved for positive $x^1$. A positive point is a steady state for some rate constants iff the vector of reaction fluxes lies in the relative interior of the flux cone, which the coordinate-hyperplane assumption guarantees, so rate constants realizing both steady states exist. The criterion reduces multistationarity to a finite sign-pattern check on two linear subspaces.

## Sources

- Mercedes Perez Millan, Alicia Dickenstein, Anne Shiu and Carsten Conradi, "Chemical Reaction Systems with Toric Steady States", Bulletin of Mathematical Biology 74 (2011), 1027–1065, <https://doi.org/10.1007/s11538-011-9685-x>; numbering as in arXiv:1102.1590: Proposition 5.2 and Theorem 5.5 (Section 5).
