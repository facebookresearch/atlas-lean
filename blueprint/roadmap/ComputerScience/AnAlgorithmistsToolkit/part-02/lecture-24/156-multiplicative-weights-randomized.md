---
article_id: af_677562e2cd3818dde3fa4585
declaration: theorem
origin: cited
statement: formalized
lean: MultiplicativeWeights.randomized_mw_expected_regret_bound
---

# Theorem (Multiplicative Weights, randomized)

Let $m_i^t$ denote the number of mistakes that expert $i$ makes in the first $t$ games and let $m^t$ denote the random variable equal to the number of mistakes that Mr.\ X makes in the first $t$ games. Then for $\epsilon < 1/2$ and for all $i$ and $t$, $\mathbf{E}(m^t) \leq \frac{\log(n)}{\epsilon} + (1+\epsilon) m_i^t$, and in particular, this holds for the $i$ that minimizes $m_i^t$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 24, Section on Multiplicative Weights](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
