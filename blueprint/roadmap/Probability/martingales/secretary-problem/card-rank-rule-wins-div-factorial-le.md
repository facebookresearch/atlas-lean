# Optimality of the threshold rule among all rank-based rules

Let $n \ge 1$. A rank-based rule is a map $s$ from the permutations $\sigma$ of
$\{0, \dots, n-1\}$ to selection times in $\{0, \dots, n-1\}$ such that $s(\sigma') = s(\sigma)$
whenever $\sigma'$ and $\sigma$ order the applicants interviewed at times $0, \dots, s(\sigma)$ in
the same way. Then for every rank-based rule $s$, the proportion of permutations $\sigma$ for which
the selected applicant is the best, $\sigma(j) \le \sigma(s(\sigma))$ for all $j$, is at most
[the win probability](win-prob.md) $P_{r_1}$ of the [optimal threshold](optimal-threshold.md)
$r_1$. Rules that may decline to select anyone are not covered; selecting the last applicant
instead never lowers the win probability.

The condition on $s$ says that the rule is non-anticipating and uses only relative ranks: whether it stops at time $t$ depends only on how the first $t + 1$ applicants compare with each other. Ferguson's argument: if it is optimal to accept a candidate at stage $j$, it is optimal to accept one at every later stage, so an optimal rule is a threshold rule, and the best threshold is $r_1$.

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics), Chapter 2, §2.1, the argument before equation (3) and equation (4).

## Background

- [Optimal stopping and the Snell envelope](../optimal-stopping-and-the-snell-envelope/README.md): the general backward-induction theory, which gives the existence of an optimal rule.
