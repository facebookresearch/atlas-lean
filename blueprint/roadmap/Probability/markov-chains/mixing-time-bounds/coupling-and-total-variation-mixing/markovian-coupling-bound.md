# Markovian couplings bound total-variation mixing

Let $P$ be a Markov kernel on a countable set $S$. A *Markovian coupling* of $P$ is a Markov kernel $Q$ on $S \times S$ whose marginals move according to $P$: from $(x,y)$ the first coordinate has law $P(x,\cdot)$ and the second $P(y,\cdot)$. It is *sticky* if the diagonal is absorbing. If $(X_t, Y_t)$ is the chain driven by $Q$ from $(x,y)$, then for all $t$

$$
\|P^t(x,\cdot) - P^t(y,\cdot)\|_{TV} \le \Pr_{(x,y)}[X_t \ne Y_t],
$$

and, for a stationary $\pi$ on finite $S$, $d(t) \le \max_{x,y} \Pr_{(x,y)}[X_t \ne Y_t]$. For a sticky coupling, $\Pr[X_t \ne Y_t]$ equals the probability that the copies have not met by time $t$ and is non-increasing in $t$.

## Proof sketch

By induction, $Q^t((x,y),\cdot)$ is a coupling of $P^t(x,\cdot)$ and $P^t(y,\cdot)$. The coupling inequality bounds the total variation of the marginals by the probability that the coupled pair differs. The worst starting pair, combined with $d \le \bar d$, gives the bound on $d(t)$, and stickiness makes the non-meeting events nested.

## Depends on

- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)
- [Distance to stationarity and total-variation mixing time](distance-to-stationarity-and-mixing-time.md)

## Proof depends on

- [Basic inequalities for total-variation mixing](total-variation-mixing-inequalities.md)
- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
