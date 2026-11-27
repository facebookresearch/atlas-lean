# Simulation lemma for T-step average returns

If two stochastic games share their stage games and every transition probability of one is within $\varepsilon/(N T R_{\max})$ of the other's, then every pair of agent and adversary policies has $T$-step average rewards within $\varepsilon$ in the two games. MDPs are the case of a one-action adversary.

**Lemma.** Let $M$ and $\bar M$ be fixed-sum two-player stochastic games (as defined on the R-max algorithm page) over the same $N$ states and the same actions, with payoffs in $[0, R_{\max}]$. Call $\bar M$ an $\alpha$-approximation of $M$ if every state carries the same stage game (hence the same rewards) in both, and for all states $s, t$ and joint actions $(a, a')$

$$P_M(s, t, a, a') - \alpha \le P_{\bar M}(s, t, a, a') \le P_M(s, t, a, a') + \alpha.$$

If $\bar M$ is an $\varepsilon/(N T R_{\max})$-approximation of $M$, then for every state $s$, every agent policy $\pi$ and every adversary policy $\rho$ (possibly history-dependent and randomized),

$$|U_{\bar M}(s, \pi, \rho, T) - U_M(s, \pi, \rho, T)| \le \varepsilon,$$

where $U(s, \pi, \rho, T)$ is the expected undiscounted average reward of the first $T$ steps from $s$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [R-max algorithm](r-max-algorithm.md)

## Proof depends on

None.

## Expansion

Fixing both policies gives, in each game, a distribution over $T$-step paths whose probability is a product of one-step transition probabilities (not a Markov chain, as the policies may depend on history). Since the average reward along a path lies in $[0, R_{\max}]$, it suffices to show $\sum_p |\Pr_M(p) - \Pr_{\bar M}(p)| \le \varepsilon/R_{\max}$. Let $h_i$ be the process that uses the transitions of $\bar M$ for its first $i$ steps and those of $M$ afterwards, so $h_0$ is the process on $M$ and $h_T$ the process on $\bar M$. The processes $h_i$ and $h_{i+1}$ differ only in step $i+1$; summing over prefixes (total mass $1$), over the at most $N$ next states (each transition probability off by at most $\alpha$) and over suffixes (mass $1$ from each next state) gives $\sum_p |\Pr_{h_i}(p) - \Pr_{h_{i+1}}(p)| \le N\alpha = \varepsilon/(T R_{\max})$, and the triangle inequality over $i = 0, \dots, T-1$ finishes the proof.

This entrywise, $T$-step form differs from the discounted [simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md), an exact identity for stationary policies of two MDPs. Kearns and Singh's earlier version for MDPs also allows payoff errors but needs an $O((\varepsilon/(N T G^T_{\max}))^2)$-approximation; Brafman and Tennenholtz present their version as an extension of it to stochastic games with a slightly improved bound.

## Sources

- R. I. Brafman and M. Tennenholtz, "R-max – A General Polynomial Time Algorithm for Near-Optimal Reinforcement Learning", *Journal of Machine Learning Research* 3 (2002), 213–231, [www.jmlr.org](https://www.jmlr.org/papers/volume3/brafman02a/brafman02a.pdf): Definition 3 and Lemma 4 with its proof (Section 4, pp. 220–222).
- M. Kearns and S. Singh, "Near-Optimal Reinforcement Learning in Polynomial Time", *Machine Learning* 49 (2002), 209–232, doi:10.1023/A:1017984413808: Definition 7 and Lemma 4 (Simulation Lemma, Section 5.2, pp. 219–221), the earlier version for MDPs.
