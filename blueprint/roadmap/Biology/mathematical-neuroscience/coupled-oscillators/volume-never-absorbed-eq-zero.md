# Non-absorbing trajectories have Lebesgue measure zero

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. Then the set of initial phase configurations $\phi \in [0, 1)^N$ whose iterates under [firing](fire.md) never enter the [absorbed set](is-absorbed.md) (i.e. all $N$ phases remain pairwise distinct after every firing) has Lebesgue measure zero.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)
- [Is Absorbed](is-absorbed.md)

## Proof depends on

- [The return map is injective](return-map-injective.md)
- [The return map expands volume](return-map-expands-volume.md)
- [Null sets pull back through firings](null-sets-pull-back-through-firings.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Sections 3.1–3.3 and 3.5, Theorem 3.1. <https://doi.org/10.1137/0150098>
