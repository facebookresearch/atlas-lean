# Positive length of planar distance sets above Hausdorff dimension one

If a compact $E\subseteq\mathbb R^2$ has Hausdorff dimension strictly greater than $1$, the Euclidean distance set $\{|x-y|:x,y\in E\}$ has positive Lebesgue length. This is the positive-length assertion, not a separate assertion that the infimum of admissible thresholds is one.

## Depends on

- [Distance set](distance-sets/distance-set.md).
- [Planar threshold property](planar-falconer-threshold/planar-threshold-property.md).

## Proof depends on

- [Falconer distance-set bound at half the ambient dimension](falconer-half-dimension-sufficiency.md), via specialization to $d=2$.

## Proof strategy

Use the proved all-dimensional bound or separately prove the planar incidence-to-distance estimate. In the specialization identify the Euclidean model, normalize $2/2=1$ in the extended-real dimension convention, and keep compactness and the strict inequality.

## Consequences
This is admissibility of the real threshold $1$, so the [least-threshold bound](planar-falconer-threshold/planar-distance-threshold-le-of-property.md) gives the upper bound $1$. Combined with [Falconer’s lower bound](falconer-s-measure-zero-distance-sets/lower-bound-falconer1985-holds.md), the planar distance threshold is exactly $1$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarFalconer.lean#L20-L22) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/073.md).
