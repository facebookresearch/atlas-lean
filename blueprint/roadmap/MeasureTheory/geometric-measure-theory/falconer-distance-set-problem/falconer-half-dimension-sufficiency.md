# Falconer distance-set bound at half the ambient dimension

For every integer $d\geq2$, if $E\subseteq\mathbb R^d$ is compact and $\dim_{\mathrm H}E>d/2$, then the set $\{|x-y|:x,y\in E\}$ has positive one-dimensional Lebesgue measure. The norm is Euclidean and the dimension comparison is strict, with no claim at equality.

## Depends on

- [Distance set](distance-sets/distance-set.md).
- [Hausdorff dimension](../dimension-functions-for-hausdorff-measures/hausdorff-dimension-function.md).

## Proof depends on

The all-dimensional proof uses a quantitative planar Furstenberg incidence estimate, distance-coordinate reductions, and summable multiscale error bounds. The earlier sufficient threshold $(d+1)/2$ does not give this bound.

## Expansion

Specify the planar point-and-direction model with its scale, separation and nonconcentration data. Prove the finite multiscale incidence inequality first, then identify the reduction from distance measures in general dimension and the step turning it into positive length of the unpinned distance set.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FalconerAllDimensions.lean#L9-L16) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/073.md).
