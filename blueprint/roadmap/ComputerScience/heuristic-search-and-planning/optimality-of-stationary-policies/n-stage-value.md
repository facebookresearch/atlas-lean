# N-stage value of a Markov policy

Let $M$ be a Markov decision process with finitely many states, rewards and transition probabilities in an ordered field, and let $\gamma$ be a discount factor. A Markov policy is a sequence $\pi = (\mu_0, \mu_1, \dots)$ of deterministic decision rules $\mu_k : S \to A$, one per stage. Its $N$-stage value with terminal value $V : S \to K$ is

$$T_{\mu_0} \big(T_{\mu_1} \big(\cdots \big(T_{\mu_{N-1}} V\big)\cdots\big)\big),$$

where $T_\mu$ is the [Bellman operator of a policy](../value-iteration/policy-bellman.md). For $N = 0$ it is $V$.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Section 1.2.1 (the $N$-stage cost function $J_{\pi,N}$ of a policy, written there for costs with a general terminal function $\bar J$).
