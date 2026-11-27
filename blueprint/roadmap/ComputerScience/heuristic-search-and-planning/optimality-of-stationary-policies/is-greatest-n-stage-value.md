# Optimality of the dynamic programming algorithm

Let $M$ be a Markov decision process with finitely many states, a nonempty finite set of actions, rewards and stochastic transition probabilities in an ordered field, and let $\gamma \ge 0$. For every horizon $N$ and terminal value $V$, the value iterate $T^N V$ is the greatest $N$-stage value of a Markov policy: every Markov policy $\pi$ satisfies $T_{\mu_0} \cdots T_{\mu_{N-1}} V \le T^N V$ in every state, and the [dynamic programming policy](dp-policy.md) attains $T^N V$ in every state at once.

This is the finite-horizon DP algorithm with stationary data, written for rewards: $T^N V(s)$ is the best expected total of $N$ discounted rewards plus the discounted terminal value $\gamma^N V$, from state $s$. The comparison is with deterministic Markov policies; randomized and history-dependent policies are not among them.

## Sources

- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.3.1, "DP Algorithm for Stochastic Finite Horizon Problems", Eq. (1.15) and the statement that the policy it produces is optimal (written for costs with stage-dependent data; the proof is omitted there).

## Informally uses

- [A Markov policy does no better than value iteration over N stages](n-stage-value-le-iterate.md)
- [The dynamic programming policy attains the value iterate](n-stage-value-dp-policy.md)
