# Deterministic ski rental with a prediction

For every $\lambda \in (0, 1)$, the deterministic algorithm that buys at the start of day $\lceil \lambda b \rceil$ if $y \ge b$ and at the start of day $\lceil b/\lambda \rceil$ if $y < b$ has competitive ratio at most $\min\left\{\frac{1 + \lambda}{\lambda},\; (1 + \lambda) + \frac{\eta}{(1 - \lambda)\,\mathrm{OPT}}\right\}$. Thus it is $(1+\lambda)$-consistent and $(1 + 1/\lambda)$-robust. At $\lambda = 1$ both cases buy on day $b$, which is the break-even strategy, and only the bound $(1+\lambda)/\lambda = 2$ remains.

## Proof sketch

Robustness: buying on day $\lceil\lambda b\rceil$ costs at most $\lambda b + b$ against an optimum of at least $\lambda b$ when $x \ge \lambda b$, and buying on day $\lceil b/\lambda\rceil$ costs at most $b/\lambda + b$ against an optimum of $b$ in the worst case. Consistency with error: if the prediction is on the correct side of $b$ the cost is at most $(1 + \lambda)\mathrm{OPT}$; if it is on the wrong side, the error is large enough, $\eta \ge |x - b|$, that the excess cost is at most $\eta/(1 - \lambda)$.

## Depends on

- [Ski rental with a predicted number of days](ski-rental-with-prediction.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018), Algorithm 2 and Theorem 2.2.
