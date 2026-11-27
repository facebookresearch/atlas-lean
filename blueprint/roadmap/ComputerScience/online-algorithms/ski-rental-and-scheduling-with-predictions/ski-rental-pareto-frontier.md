# Optimal consistency-robustness tradeoff for ski rental

Every deterministic ski-rental algorithm using a prediction that is $(1 + \lambda)$-consistent, for $\lambda \in (0, 1)$, has robustness at least $1 + \frac{b - 1}{\lambda b + 1}$, which tends to $1 + 1/\lambda$ as $b \to \infty$, so the deterministic algorithm of Purohit, Svitkina and Kumar is asymptotically Pareto-optimal. Every randomized algorithm with robustness $\gamma$ has consistency at least $\gamma \log\left(1 + \frac{1}{\gamma - 1}\right)$; with $\gamma = \frac{1}{1 - e^{-\lambda}}$ this is $\frac{\lambda}{1 - e^{-\lambda}}$, so the randomized tradeoff curve $\left(\frac{\lambda}{1 - e^{-\lambda}}, \frac{1}{1 - e^{-\lambda}}\right)$ of Purohit, Svitkina and Kumar is optimal up to lower-order terms in $b$.

## Proof sketch

For the deterministic bound, fix a prediction $y > (1 + \lambda)b$ and let $t$ be the buying day: consistency on $x = y$ forces $t \le \lambda b + 1$, and then the instance $x = t$ gives ratio $(t + b - 1)/t \ge 1 + \frac{b-1}{\lambda b + 1}$. For randomized algorithms, Wei and Zhang write the buying-day distribution as variables of an infinite linear program in which consistency and robustness are linear constraints, and determine analytically when this program is feasible.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)
- [Randomized ski rental with a prediction](ski-rental-randomized-with-prediction.md)

## Sources

- Alexander Wei, Fred Zhang, "Optimal Robustness-Consistency Trade-offs for Learning-Augmented Online Algorithms", NeurIPS (2020), arXiv:2010.11443, Theorems 1.1 and 1.2.
- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
