# Weak learnability gives a mixed hypothesis that errs on every instance with probability at most $1/2 - \gamma$

Let $h_1, \dots, h_k$ be hypotheses and $c$ a target on $n > 0$ instances, and let $\gamma \in \mathbb{R}$. Suppose that for every distribution $Q$ on the instances some hypothesis has weighted error

$$\sum_x Q(x)\, \mathbf{1}[h_j(x) \ne c(x)] \le \tfrac12 - \gamma.$$

Then some distribution $P$ on the hypotheses satisfies, for every instance $x$,

$$\sum_j P_j\, \mathbf{1}[h_j(x) \ne c(x)] \le \tfrac12 - \gamma.$$

The order of quantifiers is the point: the hypothesis may depend on $Q$, but the weighting $P$ is one for all instances. The proof applies von Neumann's minimax theorem to the [mistake matrix](mistake-matrix.md): at a saddle point $(Q^*, P^*)$, the value is at most the error of the hypothesis that weak learnability supplies for $Q^*$, and every instance's error under $P^*$ is at most the value.

## Background

- [Hedge algorithm](../hedge-algorithm/README.md): Freund and Schapire prove the minimax theorem itself by running multiplicative weights against a best-responding opponent (their Section 2.5), and obtain boosting by running the same algorithm on the dual game.

## Sources

- Y. Freund and R. E. Schapire, "Game theory, on-line prediction and boosting", *Proceedings of the Ninth Annual Conference on Computational Learning Theory* (COLT 1996), Section 4.1, the argument following equation (6).
