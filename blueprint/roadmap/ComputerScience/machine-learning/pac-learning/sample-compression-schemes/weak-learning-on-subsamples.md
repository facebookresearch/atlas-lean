# Moran-Yehudayoff weak learning on subsamples via the minimax theorem

Let $C$ be a binary class of VC dimension $d$. There are $s = O(d)$ and a proper learning map $H$ for $C$ on samples of at most $s$ examples such that, for every nonempty sample $S = (S_1, \dots, S_m)$ realizable by $C$:

1. for every probability distribution $q$ on the positions $\{1, \dots, m\}$, some subsample $Z$ of $S$ with at most $s$ examples has $H(Z)$ correct on a set of positions of $q$-probability at least $2/3$;
2. consequently there is a probability distribution $\mu$ on such subsamples such that for every position $i$, $\mu(\{Z : H(Z) \text{ is correct on } S_i\}) \ge 2/3$

(Moran and Yehudayoff, proof of Theorem 1.4 and proof of Claim 3.1).

## Proof sketch

Item 1 is the PAC sample complexity bound at error $1/3$ applied to the distribution $q$ on the examples of $S$ (Moran and Yehudayoff, Theorem 1.1). Item 2 follows from the minimax theorem for the zero-sum game in which one player picks a position and the other a subsample, with payoff the correctness indicator (Theorem 2.3).

Derived (not stated in the cited source, which uses $s = O(d)$ at error $1/3$): for $\varepsilon, \delta \in (0,1)$ and every consistent learner $A$ for $C$ reading $s \ge \frac{8}{\varepsilon}(d\ln\frac{48}{\varepsilon} + \ln\frac{4}{\delta})$ examples, every distribution $q$ on the positions admits a sequence $b \in \{1, \dots, m\}^s$ with $A(S_{b_1}, \dots, S_{b_s})$ wrong on positions of $q$-probability at most $\varepsilon$, since a random $s$-tuple drawn from $q$ succeeds with positive probability by the realizable VC upper bound; and there is a distribution $\mu$ on $\{1, \dots, m\}^s$ with $\mu(\{b : A(S \circ b) \text{ errs on } S_i\}) \le \varepsilon$ for every position $i$.

## Depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [A consistent learner for a finite class](../occam-bound-for-consistent-learners/consistent-learner.md)

## Proof depends on

- [Blumer-Ehrenfeucht-Haussler-Warmuth upper bound for consistent learners](../sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/realizable-vc-upper-bound-for-consistent-learners.md)

## Sources

- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016, Theorem 1.1, Theorem 2.3, proof of Theorem 1.4 and proof of Claim 3.1; open copy: <https://arxiv.org/abs/1503.06960>.
