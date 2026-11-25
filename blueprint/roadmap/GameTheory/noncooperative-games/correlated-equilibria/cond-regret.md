# Conditional regret

After rounds with realised profiles $s(1), \dots, s(T)$, the conditional regret of player $i$
for $j \to k$ is the total cost it would have saved by playing $k$ in every round in which it
played $j$:

$$\sum_{t \le T :\, s_i(t) = j} \bigl(c_i(s(t)) - c_i(k, s_{-i}(t))\bigr).$$

Divided by $T$ this is Hart and Mas-Colell's $D_T(j, k)$ in cost form; its positive part is the
regret $R_T(j, k)$ of (2.1c).

## Background

- [Regret against a fixed strategy](../no-regret-dynamics/regret.md): the unconditional regret,
  where every past round is changed.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, (2.1a)–(2.1c).
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §4, (1)–(4).
