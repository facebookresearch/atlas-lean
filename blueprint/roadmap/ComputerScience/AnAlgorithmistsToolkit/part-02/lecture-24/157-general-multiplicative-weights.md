---
article_id: af_90508f4d781791a7cfb036c9
declaration: theorem
origin: cited
statement: formalized
lean: MultiplicativeWeights.general_mw_regret_bound
---

# Theorem (General Multiplicative Weights)

Let $D^t$ denote the probability distribution $\{p_1^t, \ldots, p_n^t\}$ with which we pick experts to make a prediction for event $t$. Let $M(D^t, j^t)$ denote the expected value of our penalty when following the distribution $D^t$ for event $t$ and when the actual outcome is $j^t$. Then for $\epsilon \leq 1/2$ and for all $T$ and $i$, $\sum_{t=1}^{T} M(D^t, j^t) \leq \frac{\rho \log(n)}{\epsilon} + (1+\epsilon) \sum_{t:\, M(i,j^t) \geq 0} M(i, j^t) + (1-\epsilon) \sum_{t:\, M(i,j^t) < 0} M(i, j^t)$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 24, Section on Multiplicative Weights](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
