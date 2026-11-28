# Quantile threshold rules for i.i.d. prophets

For i.i.d. values with continuous distribution $F$, a *quantile threshold rule* is given by acceptance probabilities $p_1, \dots, p_n \in [0, 1]$: the gambler stops at the first index $i$ with $X_i \ge F^{-1}(1 - p_i)$, so that each value considered at step $i$ is accepted with probability exactly $p_i$. The rule depends on $F$ only through quantiles, so its ratio $\mathbb{E}[X_\tau]/\mathbb{E}[\max X_i]$ can be optimized uniformly over $F$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017).
