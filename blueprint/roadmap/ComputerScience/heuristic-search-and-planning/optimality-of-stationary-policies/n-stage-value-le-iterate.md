# A Markov policy does no better than value iteration over N stages

Let $M$ be a Markov decision process with finitely many states, finitely many actions (at least one), rewards and transition probabilities in an ordered field, with stochastic transitions, and let $\gamma \ge 0$. For every Markov policy $\pi$, every $N$ and every terminal value $V$, the $N$-stage value of $\pi$ is at most the $N$-th value iterate:

$$T_{\mu_0} \cdots T_{\mu_{N-1}} V \le T^N V \quad \text{pointwise}.$$

The proof is by induction, from the monotonicity of each $T_\mu$ and $T_\mu \le T$.

## Informally uses

- [A policy's Bellman operator is monotone](../value-iteration/policy-bellman-mono.md)
- [A policy's Bellman update is at most the optimal one](../value-iteration/policy-bellman-le-bellman.md)
