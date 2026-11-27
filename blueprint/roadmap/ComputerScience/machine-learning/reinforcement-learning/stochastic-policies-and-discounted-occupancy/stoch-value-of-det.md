# Compatibility with deterministic policies

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For every deterministic policy $\pi : S \to A$, the value of $\pi$ viewed as a stochastic policy equals its value as a deterministic policy.

## Background

- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md): the deterministic value it agrees with.
