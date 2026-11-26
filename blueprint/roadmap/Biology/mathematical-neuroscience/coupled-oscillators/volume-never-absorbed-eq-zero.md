# Non-absorbing trajectories have Lebesgue measure zero

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. Then the set of initial phase configurations $\phi \in [0, 1)^N$ whose iterates under [firing](fire.md) never enter the [absorbed set](is-absorbed.md) (i.e. all $N$ phases remain pairwise distinct after every firing) has Lebesgue measure zero.

## Expansion

Before promoting this theorem to `theorem_wanted`, formalize the intermediate return-map properties from Mirollo–Strogatz Sections 3.3–3.5:

1. Injectivity and smoothness of the $N$-oscillator return map on the open simplex of pairwise distinct non-absorbing configurations.
2. Strict volume expansion ($\det DF > 1$ on the non-absorbing simplex, generalizing the two-oscillator [firing-map derivative bound](has-deriv-at-firing-map-lt-neg-one.md)).
3. Boundedness of the domain and conclusion that the invariant non-absorbing set has measure zero.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)
- [Is Absorbed](is-absorbed.md)

## Proof depends on

- [Firing-map derivative is strictly less than minus one](has-deriv-at-firing-map-lt-neg-one.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Sections 3.3–3.5, Theorem 3.1. <https://doi.org/10.1137/0150098>
