# Two-thirds maximin share allocations always exist

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every instance a complete $\tfrac23$-MMS allocation exists. More precisely, a complete $\gamma_n$-MMS allocation exists with $\gamma_n = \frac{2 n_{\mathrm{odd}}}{3 n_{\mathrm{odd}} - 1} > \tfrac23$, where $n_{\mathrm{odd}}$ is the largest odd number at most $n$; and for every $\varepsilon > 0$ a $(1 - \varepsilon)\gamma_n$-MMS allocation can be computed in time polynomial in $n$ and $m$.

## Proof sketch

Normalize the agent under consideration to $\mu_i = 1$. Give any good worth at least $\gamma_n$ to an agent who values it so, and remove both. With two agents left, use cut and choose. Otherwise let each remaining agent take a most valued good in a forward order and then in the reverse order; if an agent's second good together with two unallocated goods is worth at least $\gamma_n$, she keeps these three goods and leaves, and the others return their goods. Finally allocate the remaining goods by envy-cycle elimination. A counting argument against the agent's maximin partition shows that every agent ends with at least $\gamma_n$.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)

## Sources

- D. Kurokawa, A. D. Procaccia, J. Wang, "Fair Enough: Guaranteeing Approximate Maximin Shares", Journal of the ACM 65(2) (2018); EC 2016.
