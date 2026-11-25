# Optimal stopping and the Snell envelope

Let $\mu$ be a finite measure, $(\mathcal{G}_k)$ a filtration and $(G_k)$ an adapted sequence of integrable real rewards, fix a horizon $N \in \mathbb{N}$, and write $\mathbb{E}$ for integration against $\mu$. Let $S$ be the Snell envelope, defined by backward induction from $S_N = G_N$ by $S_k = \max(G_k, \mathbb{E}[S_{k+1} \mid \mathcal{G}_k])$ for $k < N$, and let $\tau^*$ be the first $k \le N$ with $S_k = G_k$. Then every stopping time $\tau$ with $\tau \le N$ everywhere satisfies $\mathbb{E}[G_\tau] \le \mathbb{E}[G_{\tau^*}]$. So $\tau^*$ is optimal; with the identity $\mathbb{E}[G_{\tau^*}] = \mathbb{E}[S_0]$, also on this card, the value of the problem is $\sup_{\tau \le N} \mathbb{E}[G_\tau] = \mathbb{E}[G_{\tau^*}] = \mathbb{E}[S_0]$.

## Idea

A gain $G_n$ is observed in sequence, and one must decide when to stop, using only the information available so far, so as to maximise the expected gain. Backward induction solves the problem: at the horizon one must stop and receives $G_N$; one step earlier one compares the gain now with the expected value of going on, and so on back to time $0$. The Snell envelope built this way is the smallest supermartingale that dominates the gain. For any stopping time $\tau \le N$, optional stopping for this supermartingale gives $\mathbb{E}[G_\tau] \le \mathbb{E}[S_\tau] \le \mathbb{E}[S_0]$. The envelope stopped at $\tau^*$ is a martingale and equals the gain at $\tau^*$, so $\tau^*$ attains $\mathbb{E}[S_0]$; every optimal stopping time bounded by $N$ is at least $\tau^*$ almost surely, so $\tau^*$ is the smallest optimal time up to null sets. Started from any time $n \le N$, the same argument solves the problem conditionally on $\mathcal{G}_n$. The recursion is the prototype of Bellman's dynamic programming principle.

## Statements

- [Optimality of the first meeting time](snell-stopping-time-optimal.md)
- [Snell envelope by backward induction](snell-envelope.md): definition used in the main statement
- [The Snell envelope equals the final reward from the horizon on](snell-envelope-of-le.md): basic property: terminal values
- [Wald–Bellman recursion for the Snell envelope](snell-envelope-of-lt.md): basic property: backward recursion
- [The Snell envelope is adapted](strongly-measurable-snell-envelope.md): basic property: adaptedness
- [The Snell envelope is integrable](integrable-snell-envelope.md): basic property: integrability
- [The Snell envelope dominates the reward up to the horizon](le-snell-envelope.md): basic property: domination of the reward
- [The Snell envelope is a supermartingale](supermartingale-snell-envelope.md): basic property: supermartingale
- [Dominating supermartingales bound the Snell envelope](snell-envelope-ae-le.md): basic property: smallest dominating supermartingale
- [The Snell envelope dominates every conditional stopped reward](cond-exp-stopped-value-le-snell-envelope.md): conditional form of the upper bound
- [Every bounded stopping time earns at most the expected envelope at time zero](integral-stopped-value-le-integral-snell.md): lemma used in the proof of the main statement
- [First time the Snell envelope meets the reward](snell-stopping-time.md): definition used in the main statement
- [The first meeting time is at most the horizon](snell-stopping-time-le.md): basic property of the first meeting time
- [The first meeting time is a stopping time](is-stopping-time-snell-stopping-time.md): basic property: it is a stopping time
- [At the first meeting time the envelope equals the reward](snell-envelope-snell-stopping-time.md): lemma used in the proof
- [Before the first meeting time the envelope exceeds the reward](snell-envelope-ne-of-lt-snell-stopping-t.md): lemma used in the proof
- [Before the first meeting time the envelope is the continuation value](snell-envelope-eq-cond-exp-of-lt-snell-s.md): lemma used in the proof
- [The Snell envelope stopped at the first meeting time is a martingale](martingale-stopped-process-snell-envelop.md): lemma used in the proof: the stopped envelope is a martingale
- [The first meeting time attains the expected envelope at time zero](integral-stopped-value-snell-stopping-ti.md): lemma used in the proof of the main statement
- [The first meeting time is the smallest optimal stopping time](snell-stopping-time-le-of-optimal.md): minimality among optimal stopping times
- [First time from $n$ on that the Snell envelope meets the reward](snell-stopping-time-from.md): definition used by the conditional form
- [The first meeting time from $n$ on is a stopping time](is-stopping-time-snell-stopping-time-fro.md): lemma used for the conditional form
- [The first meeting time from $n$ on attains the envelope conditionally](snell-envelope-ae-eq-cond-exp-stopped-va.md): conditional form from time $n$
- [Stopping rules sampled on a finite nonuniform schedule](stopping-rules-sampled-on-a-finite-schedule.md)

## Background

- [Optional stopping theorem](../optional-stopping-theorem/README.md): the optimality proof applies bounded optional stopping to the envelope.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006.

## Related topics

- [Wald's equations](../wald-s-equations/wald-s-equation/wald-equation.md): the other classical use of stopping times in sums of i.i.d. variables, behind the average sample number of sequential tests.
- [Secretary problem](../secretary-problem/tendsto-win-prob-optimal-threshold.md): the classical finite-horizon example solved by backward induction.
- [Sequential tests and quickest change detection](../../hypothesis-testing/sequential-tests-and-quickest-change-detection/README.md): the statistical problems that Wald, Wolfowitz and Shiryaev reduce to optimal stopping.
- [Strong Markov property of i.i.d. sequences](../../random-walks/strong-markov-property-of-i-i-d-sequences/README.md): stopping times of i.i.d. observations.
- [Optimality of stationary policies](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/README.md): the finite-horizon dynamic programming algorithm for Markov decision processes (Bertsekas); optimal stopping of a function of a finite Markov chain is the case of two actions, stop or continue.
