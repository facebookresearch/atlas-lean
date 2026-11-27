# Conditional regrets are linear in the empirical distribution

After $T \ge 1$ rounds, the average conditional regret is a linear functional of the empirical distribution $z_T$ of
play:

$$D_T(j, k) = \sum_{s :\, s_i = j} z_T(s)\bigl(c_i(s) - c_i(k, s_{-i})\bigr).$$

So the regrets depend on the history only through $z_T$, which is the first step of the proof of
Hart and Mas-Colell's Proposition.

## Informally uses

- [Expectations under the empirical distribution](../no-regret-dynamics/sum-empirical-mul.md):
  time averages are expectations under $z_T$.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Proof of the Proposition.
