# Haussler-Littlestone-Warmuth expected error bound for the one-inclusion predictor

Let $C$ be a class of functions $X \to \{0,1\}$ such that every finite set shattered by $C$ has at most $d$ points, and let $A$ be the one-inclusion graph predictor of $C$.

1. (Transductive leave-one-out bound.) For every sample $Z$ of $m+1$ labelled points realizable by $C$, among the $m+1$ ways of holding out one example of $Z$ and predicting its label from the remaining $m$, the predictor errs on at most $d$.
2. (Expected error.) If $D$ is a distribution on $X \times \{0,1\}$ realizable by $C$ and the predictor is jointly measurable, then for $m$ i.i.d. examples $S \sim D^m$,

$$
\mathbb{E}_{S}\big[\mathrm{err}_D(A(S))\big] \le \frac{d}{m+1}.
$$

3. (Sample size.) Consequently, by Markov's inequality, $A$ is an $(\varepsilon, \delta)$-PAC learner over the distributions realizable by $C$ whenever $d/(m+1) \le \varepsilon\delta$; on a countable domain with measurable singletons the realizable sample complexity of $C$ is at most $\lceil \mathrm{VCdim}(C)/(\varepsilon\delta) \rceil$, with no $\log(1/\varepsilon)$ factor.

## Proof sketch

On a realizable sample of size $m+1$, the leave-one-out mistakes of the predictor correspond to edges of the one-inclusion graph on the realized labelings that point away from the true labeling, so their number is at most the outdegree of the true labeling, at most $d$ by the orientation lemma. By exchangeability of $D^{m+1}$, the expected error of the learner on $m$ examples equals the probability that it errs on a held-out example of $m+1$, which is the average leave-one-out error, at most $d/(m+1)$.

## Depends on

- [One-inclusion graph and the one-inclusion graph predictor](one-inclusion-graph-predictor.md)
- [The realizable distribution family](../../occam-bound-for-consistent-learners/realizable-family.md)
- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Edge density and bounded-outdegree orientations of one-inclusion graphs](one-inclusion-graph-edge-density.md)

## Sources

- D. Haussler, N. Littlestone and M. K. Warmuth, "Predicting {0, 1}-Functions on Randomly Drawn Points", Information and Computation, 1994.
