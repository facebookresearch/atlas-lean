# β at the level of denotations

Applying the denotation of $\lambda.M$ to $v$ gives the denotation of $M$ with the new bound variable valued by $v$:

$$\operatorname{app}([\![\lambda.M]\!]_{\rho, bs}, v) = [\![M]\!]_{\rho, v \cdot bs}.$$

This is Scott's graph theorem $\operatorname{app}(\operatorname{graph}(f), \cdot) = f$, applied to the continuous function that the body denotes.

## Background

- [Scott's graph theorem, part (i)](../../../Order/fixed-points-domain-theory/scott-s-graph-model/app-graph.md): the graph theorem.
- [Scott's continuity theorem for the graph model](scott-continuous-denote.md): the body denotes a continuous function.
