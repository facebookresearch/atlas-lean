---
article_id: af_f5f2e686031c2c7e9ec01933
declaration: theorem
origin: cited
lean: MultiplicativeWeights.mw_average_penalty_bound
---

# Corollary (General Multiplicative Weights)

For any $\delta$, for $\epsilon \leq \min(1/2,\, \delta/(4\rho))$, for $T = 16\rho^2 \log(n)/\delta^2$ rounds and for all $i$, the average penalty we get per round obeys: $\frac{\sum_{t=1}^{T} M(D^t, j^t)}{T} \leq \delta + \frac{\sum_{t=1}^{T} M(i, j^t)}{T}$, and in particular our average penalty per round is at most $\delta$ bigger than the average penalty of the best expert.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem (General Multiplicative Weights)](157-general-multiplicative-weights.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 24, Section on Multiplicative Weights](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
