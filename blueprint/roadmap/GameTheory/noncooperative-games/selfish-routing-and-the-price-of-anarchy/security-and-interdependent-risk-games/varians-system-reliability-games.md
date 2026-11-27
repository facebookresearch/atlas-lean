# Varian's system reliability games

Agents $i$ choose efforts $x_i \ge 0$ at unit costs $c_i > 0$ and receive benefit $v_i > 0$ when the system works; system reliability is $P(\mathrm{agg}(x))$ for a nondecreasing function $P$ with values in $[0, 1]$ and an aggregation technology: *total effort* $\mathrm{agg}(x) = \sum_i x_i$, *weakest link* $\min_i x_i$, or *best shot* $\max_i x_i$. Agent $i$ minimizes $v_i (1 - P(\mathrm{agg}(x))) + c_i x_i$. Its *stand-alone optimum* $\bar x_i$ is its best effort if it alone determined the aggregate.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Pure Nash equilibrium of a finite game](../../potential-games/is-pure-nash-2.md)

## Sources

- Hal R. Varian, "System Reliability and Free Riding", Economics of Information Security, Springer, 2004.
- Ross Anderson, Tyler Moore, Shishir Nagaraja and Andy Ozment, "Incentives and Information Security", Algorithmic Game Theory, Cambridge University Press, 2007.
