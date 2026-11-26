# Optimal consistency-robustness tradeoff for ski rental

As $b \to \infty$: every deterministic ski-rental algorithm using a prediction that is $(1 + \lambda)$-consistent, for $\lambda \in (0, 1)$, has robustness at least $1 + 1/\lambda$, so the deterministic algorithm of Purohit, Svitkina and Kumar is Pareto-optimal; and for randomized algorithms the tradeoff curve $\left(\frac{\lambda}{1 - e^{-\lambda}}, \frac{1}{1 - e^{-\lambda}}\right)$ is optimal up to lower-order terms.

## Proof sketch

For the deterministic bound, consider the prediction $y = \infty$: consistency forces buying no later than about day $\lambda b$ when $x$ is large, and then the instance $x$ equal to the buying day gives ratio $(\lambda b + b)/(\lambda b)$. For randomized algorithms, Wei and Zhang write consistency and robustness constraints on the buying-day distribution as a linear program and exhibit a dual solution, an adversary distribution over $x$, matching the exponential construction.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)
- [Randomized ski rental with a prediction](ski-rental-randomized-with-prediction.md)

## Sources

- Alexander Wei, Fred Zhang, "Optimal Robustness-Consistency Trade-offs for Learning-Augmented Online Algorithms", NeurIPS (2020), arXiv:2010.11443.
- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
