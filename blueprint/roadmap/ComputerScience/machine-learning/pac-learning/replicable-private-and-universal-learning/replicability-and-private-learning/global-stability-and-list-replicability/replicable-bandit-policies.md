# Replicable stochastic bandit policies with near-optimal regret

Call a bandit policy **$\rho$-replicable** if, under shared internal randomness and two independent realizations of the reward sequences of the same environment, it pulls exactly the same sequence of arms in both executions with probability at least $1-\rho$. For stochastic $K$-armed bandits there are $\rho$-replicable policies whose problem-dependent regret has the optimal logarithmic dependence on the horizon $T$, of the form $O\big(\mathrm{poly}(K)\,\rho^{-2} \sum_{a : \Delta_a > 0} \Delta_a^{-1}\big)$ up to factors polylogarithmic in $T$ and $K$, where $\Delta_a$ are the suboptimality gaps, and the dependence on $\rho$ cannot be improved. For stochastic linear bandits (with finitely or infinitely many arms), $\rho$-replicable policies attain problem-independent regret of order $\sqrt{T}$ up to factors polylogarithmic in $T$ and polynomial in the dimension, with dependence on $\rho$ polynomial in $1/\rho$.

## Proof sketch

Run a phased elimination algorithm with geometrically growing batches; at the end of each batch, the decision to eliminate an arm is based on empirical means rounded to a randomly shifted grid shared between executions. With grid spacing much larger than the estimation error, both executions eliminate the same arms except with probability $O(\rho/\log T)$ per phase, and the batch schedule depends only on past eliminations, so the pulled sequences coincide.

## Depends on

- [Stochastic k-armed bandits: canonical history law and regret](../../../../reinforcement-learning/multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Stochastic linear bandits and LinUCB regret](../../../../reinforcement-learning/multi-armed-bandits/stochastic-linear-bandits-and-linucb-regret.md)

## Proof depends on

- [Replicable simulation of a statistical query by randomized rounding](replicable-statistical-query-simulation.md)

## Sources

- H. Esfandiari, A. Kalavasis, A. Karbasi, A. Krause, V. Mirrokni, G. Velegkas, "Replicable Bandits", ICLR (2023), arXiv:2210.01898.
