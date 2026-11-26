# Randomized ski rental with a prediction

For every $\lambda \in (1/b, 1)$ there is a randomized ski-rental algorithm using the prediction $y$ whose expected competitive ratio is at most $\min\left\{\frac{1 + 1/b}{1 - e^{-(\lambda - 1/b)}},\; \frac{\lambda}{1 - e^{-\lambda}}\left(1 + \frac{\eta}{\mathrm{OPT}}\right)\right\}$. As $b \to \infty$ it is $\frac{\lambda}{1 - e^{-\lambda}}$-consistent and $\frac{1}{1 - e^{-\lambda}}$-robust, interpolating between $1$-consistency and the optimal randomized ratio $\frac{e}{e-1}$ without predictions.

## Proof sketch

Choose the buying day from a truncated exponential density on $[1, \lambda b]$ if $y \ge b$ and on $[1, b/\lambda]$ if $y < b$, generalizing the classical $e/(e-1)$ distribution; the expected cost against every $x$ is computed by integrating the density, and the error term is handled as in the deterministic case.

## Depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)

## Proof depends on

- [Deterministic ski rental with a prediction](ski-rental-deterministic-with-prediction.md)

## Sources

- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
