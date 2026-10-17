---
article_id: af_87fd38025d2a5e3f84e8bd94
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MinimaxLowerBound.theorem_5_11
---

# Theorem 5.11

Assume that $\Theta$ contains $M \geq 5$ hypotheses $\theta_1, \ldots, \theta_M$ such that for some constant $0 < \alpha < 1/4$, it holds (i) $|\theta_j - \theta_k|_2^2 \geq 4\phi$ and (ii) $|\theta_j - \theta_k|_2^2 \leq \frac{2\alpha\sigma^2}{n}\log(M)$. Then $$\inf_{\hat{\theta}} \sup_{\theta \in \Theta} \mathbb{P}_{\theta}\!\left(|\hat{\theta} - \theta|_2^2 \geq \phi\right) \geq \frac{1}{2} - 2\alpha.$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 5.10 (Fano's inequality)](067-fano-s-inequality.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 5.4](../../../../sources/v1/HighDimensionalStatistics.md)
