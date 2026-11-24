# The dynamic programming policy attains the value iterate

For a Markov decision process with finitely many states, a nonempty finite set of actions, rewards and transition probabilities in an ordered field, every horizon $N$ and every terminal value $V$, the $N$-stage value of the [dynamic programming policy](dp-policy.md) with terminal value $V$ is the value iterate $T^N V$. No condition on the transitions or on $\gamma$ is needed: at each stage the greedy update equals the optimal update.

## Informally uses

- [A greedy policy's Bellman update is the optimal update](../value-iteration/policy-bellman-greedy.md)
