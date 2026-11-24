# Regret matching

After the first $t + 1$ rounds, let $j$ be player $i$'s last action and $R(j, k)$ its regrets
(the positive parts of the average conditional regrets). Regret matching plays each $k \ne j$
with probability $R(j, k)/\mu$ and repeats $j$ with the remaining probability, for a fixed
constant $\mu$:
"switch next period to a different action with a probability that is proportional to the regret
for that action" (Hart 2005, §4).

## Background

- [Conditional regret](../correlated-equilibria/cond-regret.md): the regrets it uses.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, (2.2).
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §4, (5).
