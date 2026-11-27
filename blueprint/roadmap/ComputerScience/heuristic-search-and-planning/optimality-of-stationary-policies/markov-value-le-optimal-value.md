# No Markov policy beats the optimal value

Let $M$ be a Markov decision process with finitely many states, finitely many actions (at least one), real rewards and stochastic transitions, and let $0 \le \gamma < 1$. For every Markov policy $\pi$, its value is at most the optimal value $V^*$ in every state.

The $N$-stage values of $\pi$ lie below the value iterates $T^N 0$, which converge to $V^*$.

## Informally uses

- [A Markov policy does no better than value iteration over N stages](n-stage-value-le-iterate.md)
- [Value iteration converges](../value-iteration/tendsto-value-iteration.md)
