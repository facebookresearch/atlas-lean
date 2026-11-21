# Stochastic policies and discounted occupancy

Stationary stochastic policies on finite discounted Markov decision processes, Markov reward processes and their values, and discounted state visitation (AJKS Chapter 1). A deterministic policy embeds as a Dirac policy with the same value, so this layer extends value and policy iteration.

## Markov reward processes

- [One-action MDP of a Markov reward process](mrp-mdp.md)
- [The one-action MDP of a stochastic matrix is stochastic](mrp-mdp-stochastic.md)
- [Value of a Markov reward process](mrp-value.md)
- [The value of a Markov reward process solves its Bellman equation](mrp-value-eq.md)
- [Uniqueness of the value of a Markov reward process](eq-mrp-value.md)
- [Subsolutions lie below the value](le-mrp-value.md)
- [Supersolutions lie above the value](mrp-value-le.md)
- [The value is additive in the reward](mrp-value-add.md)
- [The value is homogeneous in the reward](mrp-value-smul.md)
- [The value of a negated reward](mrp-value-neg.md)
- [The value of a difference of rewards](mrp-value-sub.md)
- [Value of a constant reward](mrp-value-const.md)
- [Nonnegative rewards have nonnegative values](mrp-value-nonneg.md)
- [The value is monotone in the reward](mrp-value-mono.md)
- [Value bound](abs-mrp-value-le.md)
- [The value is the discounted sum of expected rewards](tendsto-mrp-value.md)

## Discounted state visitation

- [Discounted state visitation](visitation.md)
- [The visitation is a discounted sum of transition probabilities](tendsto-visitation.md)
- [The discounted visitation is nonnegative](visitation-nonneg.md)
- [Occupancy averages](sum-visitation-mul.md)
- [The discounted visitation is a probability distribution](sum-visitation.md)
- [The visitation charges its start state](one-sub-le-visitation-self.md)

## Stochastic policies and their values

- [Stochastic policy](stochastic-policy.md)
- [Action probability of a stochastic policy](prob.md)
- [Action probabilities are nonnegative](prob-nonneg.md)
- [Action probabilities sum to one](sum-prob.md)
- [Deterministic policy as a stochastic policy](of-det.md)
- [Action probabilities of a deterministic policy](of-det-prob.md)
- [Mixture of two stochastic policies](mix.md)
- [Action probabilities of a mixture](mix-prob.md)
- [Transition matrix of a stochastic policy](policy-kernel.md)
- [Expected reward of a stochastic policy](policy-reward.md)
- [A stochastic policy induces a stochastic matrix](policy-kernel-mem.md)
- [Value of a stochastic policy](stoch-value.md)
- [Averaged action values are the induced Bellman update](sum-prob-mul-q-value.md)
- [Bellman consistency for stochastic policies](stoch-value-eq.md)
- [Uniqueness of the value of a stochastic policy](eq-stoch-value.md)
- [Compatibility with deterministic policies](stoch-value-of-det.md)
- [No stochastic policy beats the optimal value](stoch-value-le-optimal-value.md)
- [Values of bounded rewards are bounded](stoch-value-mem-icc.md)

## Row-stochastic policies, occupancy and the performance difference lemma

- [Expected reward under a row-stochastic policy](policy-reward-2.md)
- [Advantage function of a row-stochastic policy](advantage.md)
- [Discounted state-action occupancy of a row-stochastic policy](occupancy.md)
- [Total mass of the state-action occupancy of a row-stochastic policy](sum-occupancy.md)
- [Performance difference lemma for row-stochastic policies](performance-difference.md)

## Related topics

- [Value iteration](../../../heuristic-search-and-planning/value-iteration/README.md)
- [Policy iteration](../../../heuristic-search-and-planning/policy-iteration/README.md)
- [Markov chains](../../../../Probability/markov-chains/README.md)
