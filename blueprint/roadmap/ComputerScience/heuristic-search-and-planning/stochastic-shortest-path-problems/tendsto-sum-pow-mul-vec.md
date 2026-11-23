# The value of a proper policy is its total expected reward until termination

Let $M$ be a Markov decision process with a finite set of nonterminal states, real rewards and substochastic transitions, and let $\mu$ be a proper stationary policy. Then

$$\sum_{k=0}^{N-1} P_\mu^k r_\mu \longrightarrow J_\mu \quad (N \to \infty),$$

where $J_\mu$ is the [value](ssp-value.md) of $\mu$: the value of a proper policy is the series of expected rewards collected before termination.

## Informally uses

- [The N-stage total reward](policy-bellman-iterate-zero.md)
- [Value iteration for a proper policy converges](tendsto-policy-bellman-iterate.md)
