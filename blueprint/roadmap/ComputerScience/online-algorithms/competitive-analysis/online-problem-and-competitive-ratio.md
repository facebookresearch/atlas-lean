# Online request-serving problem and competitive ratio

An *online request-serving problem* consists of a set of configurations, a set of requests, an admissible-initial-configuration predicate, a transition relation $\mathrm{ValidStep}(s, r, s')$ and a cost $\mathrm{cost}(s, r, s') \in \mathbb{N}$. A *schedule* for requests $r_1, \dots, r_T$ from $s_0$ is a sequence $s_1, \dots, s_T$ of valid steps, and its cost is the sum of step costs; $\mathrm{OPT}(s_0, \sigma)$ is the minimum cost of a schedule for $\sigma$. A *deterministic online strategy* chooses $s_t$ from $s_{t-1}$, $r_t$ and its internal memory, without seeing future requests. It is *$(c, b)$-competitive* if for every admissible $s_0$, every request sequence $\sigma$ and every schedule $S$ for $\sigma$ from $s_0$,

$$
\mathrm{cost}_{\mathrm{ALG}}(s_0, \sigma) \le c \cdot \mathrm{cost}(S) + b .
$$

Paging, list update, ski rental and the $k$-server problem are instances.

## Depends on

- [Deterministic online paging algorithm](../competitive-paging/deterministic-online-paging-algorithm.md)
- [Deterministic online list-update algorithm](../list-update-problem/deterministic-online-list-update-algorit.md)
- [Deterministic ski-rental strategy](../ski-rental-problem/strategy.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized Efficiency of List Update and Paging Rules", Communications of the ACM 28(2), 1985.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
- A. R. Karlin, M. S. Manasse, L. Rudolph and D. D. Sleator, "Competitive Snoopy Caching", Algorithmica 3, 1988.
