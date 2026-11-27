# Every policy of a discounted MDP is proper in its SSP

Let $M$ be a Markov decision process with a finite set of states $S$ and stochastic transition probabilities, and let $0 \le \gamma < 1$. Every deterministic stationary policy $\mu$ is [proper](proper.md) in the [associated SSP](to-ssp.md): from every state, the probability of not having terminated after $|S|$ stages is at most $\gamma^{|S|} < 1$.

## Sources

- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.4, item (b) ("thus making termination inevitable").

## Informally uses

- [Powers of a substochastic matrix are substochastic](transition-matrix-pow-nonneg-and-sum-le.md)
