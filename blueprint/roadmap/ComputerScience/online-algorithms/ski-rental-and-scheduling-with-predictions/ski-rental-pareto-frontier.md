# Optimal consistency-robustness tradeoff for ski rental

Every deterministic ski-rental algorithm using a prediction that is $(1 + \lambda)$-consistent, for $\lambda \in (0, 1)$, has robustness at least $1 + \frac{b - 1}{\lambda b + 1}$, which tends to $1 + 1/\lambda$ as $b \to \infty$, so the deterministic algorithm of Purohit, Svitkina and Kumar is asymptotically Pareto-optimal. For a fixed buying cost $b$, every randomized algorithm with robustness $\gamma$ has consistency at least

$$
\frac{\gamma}{b} \cdot \frac{\log\left(1 + \frac{1}{\gamma - 1}\right)}{\log\left(1 + \frac{1}{b - 1}\right)},
$$

which tends to $\gamma \log\left(1 + \frac{1}{\gamma - 1}\right)$ as $b \to \infty$, since $b \log\left(1 + \frac{1}{b-1}\right) \to 1$. The limit is not a lower bound for each fixed $b$: for $b = 2$, the algorithm that buys on day $1$ if $y \ge 2$ and otherwise rents on day $1$ and buys on day $2$ has robustness $2$ and consistency $1 < 2 \log 2$. With $\gamma = \frac{1}{1 - e^{-\lambda}}$ the limit is $\frac{\lambda}{1 - e^{-\lambda}}$: in the continuous-time limit $b \to \infty$ of Wei and Zhang's Theorem 1.2, no $\frac{1}{1 - e^{-\lambda}}$-robust randomized algorithm is better than $\frac{\lambda}{1 - e^{-\lambda}}$-consistent, so the curve $\left(\frac{\lambda}{1 - e^{-\lambda}}, \frac{1}{1 - e^{-\lambda}}\right)$ bounds every randomized consistency-robustness tradeoff in that limit.

## Proof sketch

For the deterministic bound, fix a prediction $y > (1 + \lambda)b$ and let $t$ be the buying day: consistency on $x = y$ forces $t \le \lambda b + 1$, and then the instance $x = t$ gives ratio $(t + b - 1)/t \ge 1 + \frac{b-1}{\lambda b + 1}$. For randomized algorithms, Wei and Zhang write the buying-day distribution as variables of an infinite linear program in which consistency and robustness are linear constraints, and determine analytically when this program is feasible. In the hard case $y = 2b - 1$, the buying-day distribution that keeps the robustness constraints tight gives the finite-$b$ bound above, and the limit follows as $b \to \infty$.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)

## Sources

- Alexander Wei, Fred Zhang, "Optimal Robustness-Consistency Trade-offs for Learning-Augmented Online Algorithms", NeurIPS (2020), arXiv:2010.11443, Theorems 1.1 and 1.2 and Appendix A (proof of Theorem 1.2).
- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
