# The value of a proper policy solves its Bellman equation

Let $M$ be a Markov decision process with a finite set of nonterminal states, real rewards and substochastic transitions, and let $\mu$ be a proper stationary policy. The [value](ssp-value.md) $J_\mu$ of $\mu$ satisfies $T_\mu J_\mu = J_\mu$, where $T_\mu$ is the undiscounted Bellman operator of $\mu$.

## Informally uses

- [A proper policy's Bellman operator is an |S|-stage contraction](contracting-with-policy-bellman-iterate.md)
