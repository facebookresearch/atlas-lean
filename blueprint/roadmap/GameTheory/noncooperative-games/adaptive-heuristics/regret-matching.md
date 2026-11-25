# Regret matching

After the first $t + 1$ rounds, let $j$ be player $i$'s last action and $R(j, k)$ its regrets
(the positive parts of the average conditional regrets). Regret matching gives each $k \ne j$
the weight $R(j, k)/\mu$ and gives $j$ the remaining weight $1 - \sum_{k \ne j} R(j, k)/\mu$, for
a fixed constant $\mu$. If every cost is at most $M$ in absolute value and
$\mu > 2M(|S_i| - 1)$ for every player $i$ (Hart and Mas-Colell 2000, footnote 5), every regret
is at most $2M$ and these weights form a probability distribution: player $i$ switches to each
$k \ne j$ with probability $R(j, k)/\mu$ and otherwise repeats $j$,
"switch next period to a different action with a probability that is proportional to the regret
for that action" (Hart 2005, §4). Without such a bound on $\mu$ the weights need not be
probabilities.

## Background

- [Conditional regret](../correlated-equilibria/cond-regret.md): the regrets it uses.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, (2.2) and footnote 5.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §4, (5).
