# Known-state MDP

Given a set $S$ of states whose transitions and payoffs are well estimated, the known-state MDP keeps the dynamics among states of $S$ and redirects every transition that leaves $S$ to one absorbing state. Exploration and exploitation policies are then computed in this partial model.

Let $M$ be a Markov decision process on states $1, \dots, N$ with actions $a_1, \dots, a_k$, transition probabilities $P^a_M(ij)$ and payoff means $R_M(i) \in [0, R_{\max}]$ (payoffs attached to states), and let $S$ be any subset of the states.

**Definition (induced MDP).** The induced MDP $M_S$ has states $S \cup \{s_0\}$ and

- payoffs $R_{M_S}(i) = R_M(i)$ for $i \in S$, deterministic even if the payoffs of $M$ are random, and $R_{M_S}(s_0) = 0$;
- transitions $P^a_{M_S}(s_0 s_0) = 1$ for every action $a$, so $s_0$ is absorbing;
- $P^a_{M_S}(ij) = P^a_M(ij)$ for $i, j \in S$, and $P^a_{M_S}(i s_0) = \sum_{j \notin S} P^a_M(ij)$ for $i \in S$.

**Known states.** In the E3 algorithm a state $i$ is known once each action has been executed from $i$ at least $m_{\mathrm{known}}$ times, where the visit threshold $m_{\mathrm{known}}$ meets the accuracy of the source's Lemma 5: except with probability $\delta/(3N)$ for each state, the empirical transition probabilities and the empirical payoff mean of a known state are within $O((\varepsilon/(N T G^T_{\max}))^2)$ of their true values. Here $T$ is the mixing or horizon time being targeted, $G^T_{\max}$ the largest possible $T$-step return ($G^T_{\max} \le R_{\max}$ for average returns and $G^T_{\max} \le T R_{\max}$ for discounted returns) and $\mathrm{Var}_{\max}$ the largest payoff variance.

The source's Lemma 5 prints the choice $m_{\mathrm{known}} = O((N T G^T_{\max}/\varepsilon)^4\,\mathrm{Var}_{\max}\log(1/\delta))$. A count logarithmic in $1/\delta$ is what Hoeffding-type bounds give for bounded quantities such as the transition indicators; for payoffs whose variance alone is bounded the source's derivation does not give it, so the threshold is specified by the accuracy it must meet rather than by that formula. The algorithm works with the empirical approximation $\hat M_S$ of $M_S$ built from the observed frequencies at known states.

Since $M_S$ agrees with $M$ on paths inside $S$, payoffs are nonnegative and $s_0$ pays nothing, every policy's $T$-step return in $M_S$ from a state of $S$ is at most its $T$-step return in $M$ (the source's Lemma 7).

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The accuracy in Lemma 5 is the one the source's simulation lemma needs for $T$-step returns in $\hat M_S$ and $M_S$ to differ by at most $\varepsilon$. The source derives the payoff part from the variance bound through a Chernoff-type bound; that step is not reproduced here, since a variance bound does not by itself give deviation probabilities logarithmic in $1/\delta$. Chebyshev's inequality meets the payoff accuracy with a count polynomial in $N$, $T$, $G^T_{\max}/\varepsilon$, $\mathrm{Var}_{\max}$ and $1/\delta$. R-max uses the same construction with an optimistic payoff $R_{\max}$ at the absorbing state instead of $0$, and the PAC-MDP framework generalizes it to known state-action pairs.

## Sources

- M. Kearns and S. Singh, "Near-Optimal Reinforcement Learning in Polynomial Time", *Machine Learning* 49 (2002), 209–232, doi:10.1023/A:1017984413808: Definitions 8 and 9 and Lemmas 5–7 (Sections 5.2–5.3, pp. 221–223).
