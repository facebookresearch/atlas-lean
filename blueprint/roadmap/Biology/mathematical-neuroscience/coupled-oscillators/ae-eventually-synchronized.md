# Mirollo–Strogatz synchronization of pulse-coupled oscillators

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. Then for almost every initial phase configuration $\phi \in [0, 1)^N$ (with respect to Lebesgue measure on the cube), some finite number $n$ of [firing events](fire.md) produces a [fully synchronized](synchronized.md) population: all phases of $\operatorname{fire}^{[n]}(\phi)$ are equal.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)
- [Synchronized](synchronized.md)

## Proof depends on

- [Non-absorbing trajectories have Lebesgue measure zero](volume-never-absorbed-eq-zero.md)
- [The return map is injective](return-map-injective.md)
- [The return map expands volume](return-map-expands-volume.md)
- [Null sets pull back through firings](null-sets-pull-back-through-firings.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Section 3.5, Theorems 3.1–3.2. <https://doi.org/10.1137/0150098>
