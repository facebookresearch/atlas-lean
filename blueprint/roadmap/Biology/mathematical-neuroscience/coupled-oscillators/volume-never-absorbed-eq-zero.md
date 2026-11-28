# Non-absorbing trajectories have Lebesgue measure zero

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$; until an absorption every oscillator fires alone, with strength $s(1)$. As in Section 3.1, strobe the system just after a firing: oscillator $0$ has just fired and has phase $0$, and the other $N - 1$ oscillators have phases $0 < \phi_1 < \phi_2 < \dots < \phi_{N-1} < 1$, so that the states form the set $S = \{(\phi_1, \dots, \phi_{N-1}) \in \mathbb{R}^{N-1} : 0 < \phi_1 < \dots < \phi_{N-1} < 1\}$ of (3.1). Then the set $A \subseteq S$ of states whose configuration $(0, \phi_1, \dots, \phi_{N-1})$ never enters the [absorbed set](is-absorbed.md) under [firing](fire.md) (all $N$ phases remain pairwise distinct after every firing) has $(N-1)$-dimensional Lebesgue measure zero. This is the case of $N$ groups of one oscillator each of the section-wise statement, on one ordering of the phases.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)
- [Is Absorbed](is-absorbed.md)

## Proof depends on

- [Non-absorbing configurations of a section have measure zero](never-absorbed-section-measure-zero.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Sections 3.1 and 3.5: the state space (3.1), the set $A$ of (3.6)–(3.7) and Theorem 3.1. <https://doi.org/10.1137/0150098>
