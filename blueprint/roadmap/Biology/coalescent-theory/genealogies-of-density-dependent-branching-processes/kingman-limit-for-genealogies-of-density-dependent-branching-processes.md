# Kingman limit for genealogies of density-dependent branching processes

**Model.** A density-dependent branching process with scale $K$: when the population size is $Z_t$, each individual independently, at rate $q(Z_t/K)$, dies and is replaced by a random number $L(Z_t/K)$ of offspring. Thus reproduction depends on the current density, which breaks the branching property and models competition or cooperation. Let $m(z) = \mathbb E[L(z)]$ and $m_2(z) = \mathbb E[L(z)(L(z) - 1)]$. The density $Z_t/K$ follows the ODE $\dot z = z\,q(z)(m(z) - 1)$ in the large-$K$ limit.

**Assumptions.** (Stable equilibrium) $m(z) < \infty$ for all $z > 0$, $m(1) = 1$, $q$ is continuous at $1$, and $m$ is $C^1$ at $1$ with $m'(1) < 0$. (Finite second moment) $m_2$ is continuous at $1$ and $L(z)^2$ is uniformly integrable for $z$ near $1$.

**Theorem.** Let $t > 0$ and $k \ge 1$, and start with $Z_0/K \to 1$.
1. $\sup_{0 \le s \le Kt} |Z_s/K - 1| \to 0$ in probability: the population stays at its equilibrium density over times of order $K$.
2. Conditional on $\{Z_{Kt} \ge k\}$, the coalescent of a uniform sample of $k$ individuals at time $Kt$, with time measured in units of $K$, converges in distribution (Skorokhod topology) to Kingman's $k$-coalescent run at rate $q(1)\,m_2(1)$ on $[0, t]$.

## Expansion

The proof works with moments of the population's genealogy: planar $k$-moment measures (expectations of sums over ordered $k$-tuples of individuals of a functional of their genealogy) satisfy a recursion obtained by a $k$-spine change of measure, with the population density frozen at equilibrium. As $K \to \infty$ these moments converge to the law of a planar $k$-coalescent, which, after forgetting the planar order, is Kingman's coalescent. Each pair of lineages merges at rate equal to the local birth rate $q(1)$ times the second factorial moment $m_2(1)$ of the litter size, divided by the population size $K$, the same rate as in a Cannings model with that offspring variance.

## Sources

- M. André, F. Foutel-Rodier and E. Schertzer, "Moments of density-dependent branching processes and their genealogy", arXiv:2509.05231 (2025), Theorem 1.1, Theorem 2.3, Propositions 3.1, 4.1 and 4.4, <https://doi.org/10.48550/arXiv.2509.05231>.
