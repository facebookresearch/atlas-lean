---
article_id: af_be97591fcadd42f29449b24f
declaration: def
origin: cited
statement: formalized
lean: Minimax.definition_5_1
---

# Definition 5.1

We say that an estimator $\hat{\theta}_n$ is minimax optimal over $\Theta$ if it satisfies (5.2) and there exists $C' > 0$ such that $$\inf_{\hat{\theta}} \sup_{\theta \in \Theta} \mathbb{E}_{\theta} \left[ \phi^{-1}(\Theta) |\hat{\theta} - \theta|_{2}^{2} \right] \geq C'$$ where the infimum is taken over all estimators (i.e., measurable functions of $\mathbf{Y}$). Moreover, $\phi(\Theta)$ is called minimax rate of estimation over $\Theta$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 5.1](../../../../sources/v1/HighDimensionalStatistics.md)
