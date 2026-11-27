# Nash equilibria of the heterogeneous social distancing game

**Setting.** In the social distancing game of the companion article, players have $M$ types with masses $m_1,\dots,m_M$ and distinct type parameters $b_1 < \dots < b_M$, and every best response lies in $\tilde U = \{u_m,u_M\}^N$, whose elements are $v_1,\dots,v_{2^N}$. A population state is $\pi = (p^1,\dots,p^M)$ where $p^j_l \ge 0$ is the mass of type-$j$ players using $v_l$ and $\sum_l p^j_l = m_j$; let $\Pi$ be the (compact, convex) set of such states. Let $F_{(j-1)2^N + l}(\pi)$ be the auxiliary cost of a type-$j$ player using $v_l$ when the population plays $\pi$ (it depends on $\pi$ through $\bar u$ and $I_f$), $\delta_j(\pi) = \min_l F_{(j-1)2^N+l}(\pi)$, and $\Phi(\pi) = F(\pi) - (\delta_j(\pi))_{j,l}$.

**Definition.** $\pi \in \Pi$ is a Nash equilibrium if $\pi_{(j-1)2^N+l} > 0$ implies that $v_l$ minimizes the type-$j$ cost.

**Proposition 3.**

1. $\pi$ is a Nash equilibrium iff it solves the nonlinear complementarity problem $0 \le \pi \perp \Phi(\pi) \ge 0$, i.e. $\pi \ge 0$, $\Phi(\pi) \ge 0$, $\pi^{\mathsf T}\Phi(\pi) = 0$.
2. $\pi$ is a Nash equilibrium iff $(\pi' - \pi)^{\mathsf T} F(\pi) \ge 0$ for all $\pi' \in \Pi$.
3. A Nash equilibrium exists.

**Lemma 1 (chain structure).** Ordering $\tilde U$ coordinatewise, the set of actions used by a positive mass of players at a Nash equilibrium is a chain, every maximal chain of $\tilde U$ has length $N+1$, and there are at most $N!$ of them. Hence a Nash equilibrium uses at most $N+1$ distinct actions.

**Reduced-order description.** Writing $\rho_k$ for the fraction of players choosing $u_M$ in period $k$, each $\rho \in [0,1]^N$ determines a unique population state whose actions satisfy the conclusions of Proposition 2 (a player with a larger type parameter $b$ uses a coordinatewise smaller action, and players with equal $b$ use comparable actions) and induce those fractions (Proposition 4, Corollary 2), so by Proposition 5 equilibria can be searched over $N$ variables instead of $M \cdot 2^N$.

## Expansion

The NCP and variational-inequality forms are the standard characterizations of equilibria in population games: a type may put mass only on cost-minimizing actions. $F$ is continuous in $\pi$ because the SIR states, and hence $I_f$ and $\bar u$, depend continuously on the action distribution, and $\Pi$ is compact and convex, so a solution of the variational inequality exists. The chain property follows from the coordinatewise monotonicity of best responses in the type parameter $b$: if two used actions were incomparable, the players using them would violate that ordering. The number of NCP variables grows like $2^N$, which is why the chain reduction to the per-period fractions $\rho$ matters for computation.

## Depends on

- [Bang-bang threshold best responses in social distancing games](bang-bang-threshold-best-responses-in-social-distancing-games.md)

## Sources

- I. Kordonis, A.-R. Lagos, G. P. Papavassilopoulos, "Dynamic Games of Social Distancing During an Epidemic: Analysis of Asymmetric Solutions", Dynamic Games and Applications 12 (2022) 214–236, Definition 1, Propositions 2–5, Lemma 1 and Corollary 2, <https://doi.org/10.1007/s13235-021-00403-1>, PMCID PMC8503885.
