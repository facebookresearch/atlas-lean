# Reduction to ordered instances for maximin share approximation

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. An instance is ordered if there is an enumeration $g_1, \dots, g_m$ of $M$ with $v_i(g_1) \ge v_i(g_2) \ge \dots \ge v_i(g_m)$ for every agent $i$. For every instance $I$ there is an ordered instance $I'$ on $m$ goods in which each agent's multiset of values is the same; maximin shares coincide, and any $\alpha$-MMS allocation of $I'$ can be converted in polynomial time into an $\alpha$-MMS allocation of $I$.

## Proof sketch

Define $I'$ by giving agent $i$ value $v_i'(g_k)$ equal to the $k$-th largest of her original values. Since the multiset of values is unchanged, so are maximin shares. Given an allocation of $I'$, let agents pick, in the order $g_1, g_2, \dots$ of the items they received in $I'$, their most valuable remaining original good; each agent obtains at step $k$ a good worth at least $v_i'(g_k)$, so values do not decrease.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Sources

- S. Bouveret, M. Lemaître, "Characterizing conflicts in fair division of indivisible goods using a scale of criteria", Autonomous Agents and Multi-Agent Systems 30 (2016).
- J. Garg, S. Taki, "An Improved Approximation Algorithm for Maximin Shares", EC 2020; Artificial Intelligence 300 (2021), arXiv:1903.00029.
