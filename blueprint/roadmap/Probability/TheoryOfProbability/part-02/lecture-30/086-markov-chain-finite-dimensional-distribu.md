---
article_id: af_91f7a6a7bbcec12230dc73d3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: markov_chain_finite_dimensional_distributions
---

# Theorem (Markov chain finite dimensional distributions)

If $X_n$ is any Markov chain with initial distribution $\mu$ and transition $p$, then finite-dimensional probabilities are given by $$P(X_j \in B_j,\, 0 \leq j \leq n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots \int_{B_n} p(x_{n-1}, dx_n).$$

## Depends on

- [Definition (Transition probability)](083-transition-probability.md)
- [Definition (Markov chain, general)](084-markov-chain-general.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 30/31, Markov chains section](../../../../../sources/v1/TheoryOfProbability.md)
