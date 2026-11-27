# Blum-Mansour with Hedge copies: swap regret $\eta T + N\ln N/\eta$ and $2\sqrt{T N \ln N}$

Let $X$ have $N \ge 1$ actions and losses $\ell_t \in [-1,1]^X$. Run $N$ copies of Hedge with rate $0 < \eta \le 1$; in round $t$ copy $j$ proposes a distribution $q_t(j,\cdot)$, the learner plays a stationary distribution $p_t$ of the row-stochastic matrix $q_t$ ($p_t = p_t q_t$), and copy $j$ is charged the scaled losses $p_t(j)\,\ell_t$. Then for every map $\delta : X \to X$,

$$
\sum_{t<T} \langle p_t, \ell_t\rangle \le \sum_{t<T} \sum_i p_t(i)\,\ell_t(\delta(i)) + \eta T + \frac{N \ln N}{\eta}.
$$

For $N \ge 2$ and $T \ge N \ln N$, the rate $\eta = \sqrt{N \ln N / T}$ gives swap regret at most $2\sqrt{T N \ln N}$.

## Proof sketch

By the Blum-Mansour reduction the swap regret is at most the sum of the copies' external regrets on their scaled losses. Copy $j$'s second-order Hedge bound is $\eta\sum_t p_t(j) + \ln N/\eta$ because its scaled losses have squares at most $p_t(j)$ in its own weighting; summing over $j$ gives $\eta T + N\ln N/\eta$, and balancing the two terms gives the tuned bound.

## Depends on

- [Swap regret](../../../../GameTheory/noncooperative-games/external-and-swap-regret/swap-regret.md)
- [Existence of a stationary distribution](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)

## Proof depends on

- [Black-box reduction from swap to external regret](../../../../GameTheory/noncooperative-games/blum-mansour-swap-regret-bound/exists-stationary-play-swap-regret-le-ca.md)
- [The second-order Hedge bound](../hedge-algorithm/alg-loss-le-sq.md)

## Sources

- Avrim Blum and Yishay Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8, 2007.
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, 2013.
