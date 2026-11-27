# Replicable stochastic bandit policies with near-optimal regret

Call a bandit policy **$\rho$-replicable** if, under shared internal randomness and two independent realizations of the reward sequences of the same environment, it pulls exactly the same sequence of arms in both executions with probability at least $1-\rho$. For stochastic $K$-armed bandits with rewards in $[0,1]$ there are $\rho$-replicable policies with expected regret at most $C\,K^2\rho^{-2}\sum_{a : \Delta_a > 0}\big(\Delta_a + \log(KT\log T)/\Delta_a\big)$, where $\Delta_a$ are the suboptimality gaps, which keeps the optimal logarithmic dependence on the horizon $T$; the $\rho^{-2}$ dependence cannot be improved, by the replicable coin-problem lower bound. For stochastic $d$-dimensional linear bandits with rewards $\langle\theta^\star, a\rangle + \eta_t$, $\eta_t$ zero-mean $1$-subgaussian, $\|\theta^\star\|_2 \le 1$ and $\sup_{a}\|a\|_2 \le 1$, the rates differ between finite and infinite action sets. With $K$ arms, a $\rho$-replicable policy has expected regret at most $C\,K^2\rho^{-2}\sqrt{dT\log(KT)}$, the $\sqrt{T}$ rate with a $K^2$ overhead. With infinitely many arms that bound is vacuous after discretization, since a fine net has too many arms: running the finite-arm policy on a $T^{-1/(4d+2)}$-net gives regret at most $C\,T^{(4d+1)/(4d+2)}\sqrt{d\log T}/\rho^2$, a different exponent, and a replicable least-squares policy recovers regret $C\,d^4 \sqrt{T}\,\rho^{-2}$ up to factors polylogarithmic in $T$ and $d$.

## Proof sketch

Run a phased elimination algorithm with geometrically growing batches; at the end of each batch, the decision to eliminate an arm is based on empirical means rounded to a randomly shifted grid shared between executions. With grid spacing much larger than the estimation error, both executions eliminate the same arms except with probability $O(\rho/\log T)$ per phase, and the batch schedule depends only on past eliminations, so the pulled sequences coincide.

## Depends on

- [Stochastic k-armed bandits: canonical history law and regret](../../../../reinforcement-learning/multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Stochastic linear bandits and LinUCB regret](../../../../reinforcement-learning/multi-armed-bandits/stochastic-linear-bandits-and-linucb-regret.md)

## Proof depends on

- [Replicable bounded-mean and coin-bias estimation](../../../replicable-learning/replicable-mean-estimation.md)
- [Replicability costs a quadratic factor in the replicability parameter](replicable-coin-problem-lower-bound.md)

## Sources

- H. Esfandiari, A. Kalavasis, A. Karbasi, A. Krause, V. Mirrokni, G. Velegkas, "Replicable Bandits", ICLR (2023), arXiv:2210.01898, Definition 1, Theorems 3, 4, 6 and 10, Corollary 12.
