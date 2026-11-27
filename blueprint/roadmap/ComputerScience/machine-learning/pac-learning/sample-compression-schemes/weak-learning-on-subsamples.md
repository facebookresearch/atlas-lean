# Moran-Yehudayoff weak learning on subsamples via the minimax theorem

Let $C$ be a binary class whose finite shattered sets have at most $d$ points, and let $A$ be a consistent learner for $C$ reading $s \ge \frac{8}{\varepsilon}(d\ln\frac{48}{\varepsilon} + \ln\frac{4}{\delta})$ examples, where $\varepsilon, \delta \in (0,1)$. Let $S = (S_1, \dots, S_m)$ be a nonempty sample realizable by $C$.

1. For every probability distribution $q$ on the positions $\{1, \dots, m\}$, some sequence $b \in \{1, \dots, m\}^s$ has $A(S_{b_1}, \dots, S_{b_s})$ wrong on a set of positions of $q$-probability at most $\varepsilon$.
2. Consequently there is a probability distribution $\mu$ on $\{1, \dots, m\}^s$ such that for every position $i$, $\mu(\{b : A(S \circ b) \text{ errs on } S_i\}) \le \varepsilon$.

## Proof sketch

Item 1 is the realizable VC upper bound applied to the distribution $q$ on the examples of $S$: a random $s$-tuple drawn from $q$ succeeds with positive probability. Item 2 follows from the minimax theorem for the zero-sum game in which one player picks a position and the other a subsample, with payoff the error indicator.

## Depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [A consistent learner for a finite class](../occam-bound-for-consistent-learners/consistent-learner.md)

## Proof depends on

- [Blumer-Ehrenfeucht-Haussler-Warmuth upper bound for consistent learners](../sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/realizable-vc-upper-bound-for-consistent-learners.md)

## Sources

- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016.
