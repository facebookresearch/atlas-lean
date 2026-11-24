# The SSP value of a discounted MDP's policy is its discounted value

Let $M$ be a Markov decision process with finitely many states, real rewards and stochastic transition probabilities, and let $0 \le \gamma < 1$. For every deterministic stationary policy $\mu$, the [SSP value](ssp-value.md) of $\mu$ in the [associated SSP](to-ssp.md) is the discounted [value of the policy](../value-iteration/policy-value.md) $\mu$ in $M$. Results for SSP problems therefore specialize to discounted problems.

## Sources

- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.4, item (b) ("algorithms and analysis for SSP problems can be easily adapted to discounted problems").

## Informally uses

- [Every policy of a discounted MDP is proper in its SSP](proper-to-ssp.md)
- [Uniqueness of the value of a proper policy](eq-ssp-value-of-policy-bellman-eq.md)
- [The undiscounted Bellman operator of the SSP is the discounted one](policy-bellman-to-ssp.md)
