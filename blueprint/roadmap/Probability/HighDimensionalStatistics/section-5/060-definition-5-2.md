---
article_id: af_4353dc6ce6a62097f25f8664
declaration: def
origin: cited
statement: formalized
lean: Minimax.definition_5_2
---

# Definition 5.2

We say that an estimator $\hat{\theta}$ is minimax optimal over $\Theta$ if it satisfies either (5.2) or (5.3) and there exists $C' > 0$ such that $$\inf_{\hat{\theta}} \sup_{\theta \in \Theta} \mathbb{P}_{\theta} \left[ |\hat{\theta} - \theta|_2^2 > \phi(\Theta) \right] \geq C'$$ where the infimum is taken over all estimators (i.e., measurable functions of $\mathbf{Y}$). Moreover, $\phi(\Theta)$ is called minimax rate of estimation over $\Theta$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 5.1](../../../../sources/v1/HighDimensionalStatistics.md)
