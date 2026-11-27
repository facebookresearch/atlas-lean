# Randomized ski rental with a prediction

For every integer $b \ge 2$ and every $\lambda \in (1/b, 1)$ there is a randomized ski-rental algorithm using the prediction $y$ whose expected competitive ratio is at most $\min\left\{\frac{1 + 1/b}{1 - e^{-(\lambda - 1/b)}},\; \frac{\lambda}{1 - e^{-\lambda}}\left(1 + \frac{\eta}{\mathrm{OPT}}\right)\right\}$. As $b \to \infty$ it is $\frac{\lambda}{1 - e^{-\lambda}}$-consistent and $\frac{1}{1 - e^{-\lambda}}$-robust, interpolating between $1$-consistency and the optimal randomized ratio $\frac{e}{e-1}$ without predictions.

## Proof sketch

If $y \ge b$, let $m = \lfloor \lambda b \rfloor$, and otherwise $m = \lceil b/\lambda \rceil$; buy at the start of day $j \in \{1, \dots, m\}$ with probability proportional to $\left(\frac{b-1}{b}\right)^{m-j}$, a truncated version of the classical $e/(e-1)$ distribution. The expected cost against every $x$ is computed by summing the geometric series, and the error term is handled as in the deterministic case. The guarantee is against an oblivious adversary.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018), Algorithm 3, Theorem 2.3 and Lemma A.2.
