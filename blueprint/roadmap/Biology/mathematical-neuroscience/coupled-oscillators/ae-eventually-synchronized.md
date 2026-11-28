# Mirollo–Strogatz synchronization of pulse-coupled oscillators

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let every oscillator fire with strength $\varepsilon > 0$, a group formed by absorptions firing with the sum of its members' strengths: the group pulse strengths are $s(k) = k \varepsilon$ for every group size $k \ge 1$, as in the iteration that defines the set $B$ of Theorem 3.2. As in Section 3.1, strobe the system just after a firing: oscillator $0$ has just fired and has phase $0$, and the other $N - 1$ oscillators have phases $0 < \phi_1 < \phi_2 < \dots < \phi_{N-1} < 1$, so that the states form the set $S = \{(\phi_1, \dots, \phi_{N-1}) \in \mathbb{R}^{N-1} : 0 < \phi_1 < \dots < \phi_{N-1} < 1\}$ of (3.1). Then for almost every $(\phi_1, \dots, \phi_{N-1}) \in S$, with respect to $(N-1)$-dimensional Lebesgue measure, some finite number $n$ of [firing events](fire.md) produces a [fully synchronized](synchronized.md) population: all phases of $\operatorname{fire}^{[n]}(0, \phi_1, \dots, \phi_{N-1})$ are equal.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)
- [Synchronized](synchronized.md)

## Proof depends on

- [Non-absorbing trajectories have Lebesgue measure zero](volume-never-absorbed-eq-zero.md)
- [Non-absorbing configurations of a section have measure zero](never-absorbed-section-measure-zero.md)
- [Null sets pull back through firings](null-sets-pull-back-through-firings.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Sections 3.1 and 3.5: the state space (3.1), Theorems 3.1–3.2 and the definition of $B$. <https://doi.org/10.1137/0150098>
