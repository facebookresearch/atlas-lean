# Uniqueness of the value of a proper policy

Let $M$ be a Markov decision process with a finite set of nonterminal states, real rewards and substochastic transitions, and let $\mu$ be a proper stationary policy. If $V : S \to \mathbb{R}$ satisfies $T_\mu V = V$, then $V$ is the [value](ssp-value.md) of $\mu$.

## Informally uses

- [A proper policy's Bellman operator is an |S|-stage contraction](contracting-with-policy-bellman-iterate.md): a fixed point of $T_\mu$ is a fixed point of the contraction $T_\mu^{|S|}$, which has only one.
