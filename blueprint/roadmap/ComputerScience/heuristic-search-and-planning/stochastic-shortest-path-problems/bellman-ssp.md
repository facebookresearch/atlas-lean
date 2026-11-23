# Bellman's equation for stochastic shortest path problems

Let $M$ be a Markov decision process with a finite set $S$ of nonterminal states, finitely many actions (at least one, every action allowed in every state), real rewards and substochastic transitions. Write $T$ for the undiscounted Bellman optimality operator, which maximizes reward, and $T_\mu$ for the undiscounted Bellman operator of a deterministic stationary policy $\mu$. Assume the strong SSP conditions:

1. some deterministic stationary policy is [proper](proper.md);
2. for every improper deterministic stationary policy $\mu$ there is a state $s$ from which the $N$-stage total rewards $(T_\mu^N 0)(s)$ are unbounded below. Equivalently, the $\limsup$ of the $N$-stage costs (negative rewards) is $+\infty$ there. The hypothesis is stated in terms of a $\limsup$, not a limit.

Then there is $V^* : S \to \mathbb{R}$ such that

- $V^*$ is the unique solution of Bellman's equation $T V^* = V^*$;
- value iteration converges: $T^k J \to V^*$ for every $J$;
- no deterministic stationary policy does better than $V^*$: for every such policy $\mu$, proper or improper, and every state $s$, $\liminf_{N\to\infty} (T_\mu^N 0)(s) \le V^*(s)$ (precisely: for every $\varepsilon > 0$, $(T_\mu^N 0)(s) \le V^*(s) + \varepsilon$ for infinitely many $N$). This is the reward form of Bertsekas's $J^*(s) \le J_\mu(s)$, where $J^* = -V^*$ and $J_\mu(s)$ is the $\limsup$ of the $N$-stage costs;
- in particular every proper policy $\mu$ has [reward value](ssp-value.md) $V_\mu \le V^*$;
- a deterministic stationary policy $\mu$ satisfies $T_\mu V^* = T V^*$ if and only if $\mu$ is proper and $V_\mu = V^*$, that is, if and only if $\mu$ is optimal among deterministic stationary policies.

The comparison here is only over deterministic stationary policies, whereas the source's $J^*$ is optimal over all policies. The source also allows the available actions to depend on the state.

## Sources

- D. P. Bertsekas, [*Abstract Dynamic Programming*](https://stuff.mit.edu/~dimitrib/AbstractDP_ED3_TEXT_2021.pdf), 3rd ed., Athena Scientific (2022), Example 1.2.6 and §3.5.1, which discuss the results of D. P. Bertsekas and J. N. Tsitsiklis, *An analysis of stochastic shortest path problems*, Math. Oper. Res. 16(3) (1991), 580–595.

## Background

- [Value iteration for a proper policy converges](tendsto-policy-bellman-iterate.md): the single-policy case.
- [Optimality of stationary policies](../optimality-of-stationary-policies/is-greatest-markov-value.md): the discounted analogue, where every policy is "proper" and $T$ is a contraction.
