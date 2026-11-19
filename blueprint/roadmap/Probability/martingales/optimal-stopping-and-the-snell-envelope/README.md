# Optimal stopping and the Snell envelope

A gain $G_n$ is observed sequentially, adapted to a filtration $(\mathcal G_n)$, and one must choose a stopping time $\tau \le N$ to maximise $\mathsf E\, G_\tau$. Following Peskir and Shiryaev (*Optimal Stopping and Free-Boundary Problems*, 2006, Chapter I, §1.1), the problem is solved by backward induction: the Snell envelope $S_N = G_N$, $S_n = \max(G_n, \mathsf E[S_{n+1} \mid \mathcal G_n])$ is the smallest supermartingale dominating the gain, the first time $\tau^*$ at which $S_n = G_n$ is optimal, $\mathsf E\, G_{\tau^*} = \mathsf E\, S_0$ is the value, and the envelope stopped at $\tau^*$ is a martingale. Integrability of every $G_n$ (the book's condition (1.1.3) for a finite horizon) is assumed throughout. This is Theorem 1.2: the conditional statements (1.1.9)–(1.1.10) at every time $n \le N$, and the optimality, minimality and martingale statements (1.1.11)–(1.1.14) at time $0$. The infinite-horizon theory with essential suprema is Theorems 1.4 and 1.6 of the book. The recursion is the prototype of Bellman's dynamic programming principle (Peskir–Shiryaev, p. 6).

## The envelope

Backward induction defines the envelope; it is adapted, integrable, a supermartingale dominating the gain, and the smallest such sequence.

- [Snell envelope by backward induction](snell-envelope.md)
- [The Snell envelope equals the final reward from the horizon on](snell-envelope-of-le.md)
- [Wald–Bellman recursion for the Snell envelope](snell-envelope-of-lt.md)
- [The Snell envelope is adapted](strongly-measurable-snell-envelope.md)
- [The Snell envelope is integrable](integrable-snell-envelope.md)
- [The Snell envelope is a supermartingale](supermartingale-snell-envelope.md)
- [The Snell envelope dominates the reward up to the horizon](le-snell-envelope.md)
- [Dominating supermartingales bound the Snell envelope](snell-envelope-ae-le.md)

## The optimal stopping time

The first time the envelope meets the gain is a stopping time; it is optimal and the smallest optimal time, and the envelope stopped there is a martingale.

- [First time the Snell envelope meets the reward](snell-stopping-time.md)
- [The first meeting time is at most the horizon](snell-stopping-time-le.md)
- [The first meeting time is a stopping time](is-stopping-time-snell-stopping-time.md)
- [At the first meeting time the envelope equals the reward](snell-envelope-snell-stopping-time.md)
- [Before the first meeting time the envelope exceeds the reward](snell-envelope-ne-of-lt-snell-stopping-t.md)
- [Before the first meeting time the envelope is the continuation value](snell-envelope-eq-cond-exp-of-lt-snell-s.md)
- [Every bounded stopping time earns at most the expected envelope at time zero](integral-stopped-value-le-integral-snell.md)
- [The first meeting time attains the expected envelope at time zero](integral-stopped-value-snell-stopping-ti.md)
- [Optimality of the first meeting time](snell-stopping-time-optimal.md)
- [The first meeting time is the smallest optimal stopping time](snell-stopping-time-le-of-optimal.md)
- [The Snell envelope stopped at the first meeting time is a martingale](martingale-stopped-process-snell-envelop.md)

## The conditional solution at every time

Backward induction solves the problem "in a stochastic sense" (Peskir–Shiryaev, p. 3): from every time $n \le N$ on, $S_n$ dominates $\mathsf E[G_\tau \mid \mathcal G_n]$ for every stopping time $n \le \tau \le N$, with equality for the first time $\tau_n \ge n$ at which $S = G$.

- [First time from $n$ on that the Snell envelope meets the reward](snell-stopping-time-from.md)
- [The first meeting time from $n$ on is a stopping time](is-stopping-time-snell-stopping-time-fro.md)
- [The Snell envelope dominates every conditional stopped reward](cond-exp-stopped-value-le-snell-envelope.md)
- [The first meeting time from $n$ on attains the envelope conditionally](snell-envelope-ae-eq-cond-exp-stopped-va.md)

## Related topics

- [Optional stopping theorem](../optional-stopping-theorem/README.md): the optimality proof applies bounded optional stopping to the envelope.
- [Wald's equations](../wald-s-equations/README.md): the other classical use of stopping times in sums of i.i.d. variables, behind the average sample number of sequential tests.
- [Secretary problem](../secretary-problem/README.md): the classical finite-horizon example solved by backward induction.
- [Sequential tests and quickest change detection](../../hypothesis-testing/sequential-tests-and-quickest-change-detection/README.md): the statistical problems that Wald, Wolfowitz and Shiryaev reduce to optimal stopping.
- [Strong Markov property of i.i.d. sequences](../../random-walks/strong-markov-property-of-i-i-d-sequences/README.md): stopping times of i.i.d. observations.
- [Optimality of stationary policies](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/README.md): the finite-horizon dynamic programming algorithm for Markov decision processes (Bertsekas); optimal stopping of a function of a finite Markov chain is the case of two actions, stop or continue.
