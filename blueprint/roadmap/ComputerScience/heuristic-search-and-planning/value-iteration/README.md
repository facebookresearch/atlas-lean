# Value iteration

- [Markov decision process](mdp.md)
- [Stochastic Markov decision process](stochastic.md)
- [Q-value of an action](q-value.md)
- [Bellman optimality operator](bellman.md)
- [Bellman operator of a policy](policy-bellman.md)
- [Value iteration](value-iteration.md)
- [Tabulated value iteration](value-iteration-vec.md)
- [Greedy policy](greedy.md)
- [Tabulated value iteration is correct](value-iteration-vec-get.md)

## Order and Lipschitz facts, in any ordered field

- [Action values are monotone in the value estimate](q-value-mono.md)
- [The Bellman optimality operator is monotone](bellman-mono.md)
- [A policy's Bellman operator is monotone](policy-bellman-mono.md)
- [A policy's Bellman update is at most the optimal one](policy-bellman-le-bellman.md)
- [The greedy action attains the Bellman maximum](q-value-greedy.md)
- [A greedy policy's Bellman update is the optimal update](policy-bellman-greedy.md)
- [Action values are $\gamma$-Lipschitz in the value estimate](abs-q-value-sub-le.md)
- [The Bellman optimality operator is $\gamma$-Lipschitz in the sup norm](abs-bellman-sub-le.md)
- [A policy's Bellman operator is $\gamma$-Lipschitz in the sup norm](abs-policy-bellman-sub-le.md)

## Real values: contraction, value iteration, optimality

- [Bellman's operator is a contraction](bellman-contracting.md)
- [A policy's Bellman operator is a contraction](policy-bellman-contracting.md)
- [Optimal value of a discounted Markov decision process](optimal-value.md)
- [Value of a policy](policy-value.md)
- [The optimal value solves the Bellman optimality equation](bellman-optimal-value.md)
- [Uniqueness of the solution of the Bellman optimality equation](eq-optimal-value-of-bellman-eq.md)
- [A policy's value satisfies its Bellman equation](policy-bellman-policy-value.md)
- [Uniqueness of the solution of a policy's Bellman equation](eq-policy-value-of-policy-bellman-eq.md)
- [Value iteration converges](tendsto-value-iteration.md)
- [A priori error bound for value iteration](dist-value-iteration-le.md)
- [Stopping test](dist-optimal-value-le.md)
- [No deterministic policy beats the optimal value](policy-value-le-optimal-value.md)
- [A greedy policy for the optimal value is optimal](policy-value-greedy.md)

## Related topics

- [Stochastic policies and discounted occupancy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/README.md)
- [Greedy policies of approximate values](../../machine-learning/reinforcement-learning/greedy-policies-of-approximate-values/README.md)
- [Optimality of stationary policies](../optimality-of-stationary-policies/README.md)
