# Secretary problem: the $1/e$ law

For $n \ge 1$ applicants and a threshold $1 \le r \le n$, let $T_r = \sum_{j=r}^{n-1} 1/j$ and $P_r = (1 + (r-1) T_r)/n$; $P_r$ is the probability that the threshold rule (reject the first $r - 1$ applicants, then accept the first one better than all before) selects the best applicant when all $n!$ interview orders are equally likely. Let $r_1(n) = \min\{r \ge 1 : T_r \le 1\}$ be the optimal threshold. Then $P_{r_1(n)} \to 1/e$ as $n \to \infty$.

## Idea

Applicants are interviewed in random order; after each interview one may only compare the applicant with those already seen, and must accept or reject at once. The goal is to select the best one. The best rule waits: it lets about $n/e$ applicants go by, then takes the first one better than all of them. However large $n$ is, it wins with probability close to $1/e \approx 0.368$. Ferguson shows that an optimal rule based on relative ranks is a threshold rule, and among threshold rules $r_1$ is best; both facts are on this card. For the limit, comparing the harmonic tail with an integral gives $T_r \approx \log((n-1)/(r-1))$, so $T_{r_1} \approx 1$ forces $r_1/n \to 1/e$. Then $1 - 1/(r_1 - 1) < T_{r_1} \le 1$ squeezes $P_{r_1}$ between $(r_1 - 1)/n$ and $r_1/n$, and both tend to $1/e$.

## Statements

- [The $1/e$ law of the secretary problem](tendsto-win-prob-optimal-threshold.md)
- [Harmonic tail of the secretary problem](harmonic-tail.md): definition used in the main statement
- [Win probability of a threshold rule in the secretary problem](win-prob.md): definition used in the main statement
- [Increment of the win probability of threshold rules](win-prob-succ-sub.md): lemma used for the optimal threshold
- [Win probability of a threshold rule in the random-order model](card-threshold-rule-wins-div-factorial.md): win probability in the random-order model
- [Optimal threshold of the secretary problem](optimal-threshold.md): definition used in the main statement
- [The optimal threshold rule of the secretary problem](win-prob-le-win-prob-optimal-threshold.md): optimal threshold among threshold rules
- [Optimality of the threshold rule among all rank-based rules](card-rank-rule-wins-div-factorial-le.md): optimality among all rank-based rules (stronger)
- [Integral upper bound for the harmonic tail](harmonic-tail-le-log-sub-log.md): lemma used for the asymptotics
- [Integral lower bound for the harmonic tail](log-sub-log-le-harmonic-tail.md): lemma used in the proof of the main statement
- [The optimal threshold is asymptotically $n/e$](tendsto-optimal-threshold-div.md): threshold asymptotics $n/e$

## Background

- [Optimal stopping and the Snell envelope](../optimal-stopping-and-the-snell-envelope/README.md): the general finite-horizon theory; Ferguson's backward-induction equation is the Snell envelope of the reward $y_j = j/n$ on a candidate.

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics).
