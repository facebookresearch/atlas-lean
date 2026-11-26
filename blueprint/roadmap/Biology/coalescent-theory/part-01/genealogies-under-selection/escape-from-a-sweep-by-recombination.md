# Joint escape of sampled lineages from a selective sweep

In the logistic sweep model of a favored allele $B$ rising in frequency from $1/(2N)$ to $1 - 1/(2N)$, with a neutral locus at recombination probability $r$, Durrett and Schweinsberg (2004) show that a single lineage escapes the sweep with probability tending to $1 - e^{-a}$ when $N \to \infty$ and $r\log(2N)/s \to a$ (their Proposition 1). For $k$ lineages sampled in $B$ at the end of the sweep, let $p_{k,m}$ be the probability that they have $m$ distinct ancestors at its start. If moreover $s(\log N)^2 \to \infty$, then for $j \ge 2$

$$p_{k, k-j+1} \to \binom{k}{j} p^j (1 - p)^{k-j}, \qquad p = e^{-a},$$

and $p_{k,k} \to (1 - p)^k + kp(1 - p)^{k-1}$ (Proposition 2): the trapped lineages coalesce into one and are trapped independently. To account for the random early phase of the sweep, they approximate its effect on a sample by a stick-breaking (paintbox) partition: with $M = \lfloor 2Ns \rfloor$, independent Bernoulli variables $\xi_l$ with mean $r/s$ and independent $W_l \sim \mathrm{Beta}(1, l - 1)$ for $2 \le l \le M$, set $V_l = \xi_l W_l$, $T_1 = \prod_{l=2}^M (1 - V_l)$ and $T_l = V_l\prod_{m=l+1}^M(1 - V_m)$, split $[0, 1]$ into consecutive intervals of lengths $T_1, \dots, T_M$, and put two sampled lineages in the same block when independent uniform variables attached to them fall into the same interval; the block for the first interval is marked as not having escaped with probability $s/(r(1 - s) + s)$. This rests on a Yule-process approximation of the lineages of $B$ with an infinite line of descent, with at most one recombination per Yule epoch, and allows several blocks with more than one lineage.

## Depends on

- [Logistic trajectory of a selective sweep](../../../detecting-selection/selective-sweeps/sweep-traj.md)
- [Probability of escaping a selective sweep](../../../detecting-selection/composite-selection-scores/escape-prob.md)

## Expansion

1. The single-lineage escape probability as an integral over the logistic path (equation (4)) and its limit $1 - e^{-a}$ (Proposition 1).
2. The joint law of trapping for $k$ lineages and the binomial limit (Proposition 2).
3. The stick-breaking partition: the Yule-process approximation, the Beta$(1, l - 1)$ fractions, the Bernoulli recombination indicators and the marking of the non-escaping block.
4. The probabilities for one and two lineages under the stick-breaking approximation (Proposition 3), as a separate statement.

## Sources

- R. Durrett and J. Schweinsberg, Approximating selective sweeps, Theor. Popul. Biol. 66 (2004), 129–138, equation (4), Propositions 1–3 and the stick-breaking construction. <https://doi.org/10.1016/j.tpb.2004.04.002>
