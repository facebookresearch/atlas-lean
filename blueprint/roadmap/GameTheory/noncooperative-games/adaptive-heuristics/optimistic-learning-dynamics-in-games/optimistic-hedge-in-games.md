# Optimistic Hedge in a repeated normal-form game

Fix a finite normal-form game with players $1, \dots, m$, where player $i$ has $n_i$ actions and loss functions $\ell_i$ with values in $[0, 1]$. In round $t$, player $i$ plays a mixed strategy $x_i^t \in \Delta_{n_i}$ and observes the expected loss vector $\ell_i^t \in [0, 1]^{n_i}$ against the others' strategies. Optimistic Hedge with step size $\eta > 0$ sets $x_i^1$ uniform and

$$
x_i^{t+1}(a) \propto x_i^{t}(a)\, \exp\!\bigl(-\eta\,(2 \ell_i^{t}(a) - \ell_i^{t-1}(a))\bigr),
$$

with $\ell_i^{0} = 0$; that is, it plays Hedge on the cumulative losses plus a recency prediction that the next loss equals the last one. Player $i$'s regret after $T$ rounds is $\max_{a} \sum_{t \le T} \langle \ell_i^t, x_i^t - e_a\rangle$.

## Depends on

- [Loss of the Hedge algorithm](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss.md)
- [Regret against a fixed strategy](../../no-regret-dynamics/regret.md)
- [External regret](../../../not-yet-classified/part-02/regret/external-regret.md)

## Sources

- A. Rakhlin, K. Sridharan, "Optimization, Learning, and Games with Predictable Sequences", NeurIPS 2013, arXiv:1311.1869.
- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407.
- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924.
