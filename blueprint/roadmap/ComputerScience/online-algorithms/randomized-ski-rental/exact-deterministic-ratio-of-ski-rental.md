# Exact deterministic competitive ratio of ski rental

In the discrete ski-rental problem with integer purchase price $B \ge 1$ (renting costs $1$ per day), the break-even strategy (rent for $B - 1$ days and buy on day $B$) satisfies $B \cdot \mathrm{ALG} \le (2B - 1) \cdot \mathrm{OPT}$ on every number of days, i.e. it is $(2 - 1/B)$-competitive with additive constant $0$, and for every deterministic strategy there is a number of days with $\mathrm{OPT} \ge 1$ and $(2B - 1)\,\mathrm{OPT} \le B \cdot \mathrm{ALG}$. Hence $2 - 1/B$ is the exact deterministic ratio without additive constant.

## Proof sketch

If the season lasts $n < B$ days both pay $n$; otherwise the break-even strategy pays $2B - 1$ against $\mathrm{OPT} = B$. A deterministic strategy is a rent-then-buy threshold $t$; the adversary ends the season the day the strategy buys, giving cost $t + B$ against $\min(t+1, B)$, which is minimized in ratio at $t = B - 1$.

## Depends on

- [Break-even strategy](../ski-rental-problem/break-even.md)
- [Offline optimum for ski rental](../ski-rental-problem/opt.md)
- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Proof depends on

- [Lower bound for deterministic ski rental, weak form](../ski-rental-problem/exists-cost-ge.md)

## Sources

- A. R. Karlin, M. S. Manasse, L. Rudolph and D. D. Sleator, "Competitive Snoopy Caching", Algorithmica 3, 1988.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
