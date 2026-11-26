# Full Hausdorff dimension of Euclidean Kakeya sets in every dimension

For every integer $n\geq2$, let $F\subseteq\mathbb R^n$ contain a whole unit segment in each direction: for each $|\omega|=1$ some $x$ has $\{x+t\omega:-1/2\leq t\leq1/2\}\subseteq F$. Then $\dim_{\mathrm H} F=n$. The set $F$ is not assumed measurable, compact, or bounded.

## Depends on

- [Hausdorff dimension](../../../../MeasureTheory/geometric-measure-theory/dimension-functions-for-hausdorff-measures/hausdorff-dimension-function.md).

## Proof depends on
- [Kakeya maximal estimate](kakeya-maximal-every-positive-loss.md), to control directional coverage at each scale.

## Proof strategy

Convert an arbitrary Hausdorff cover to scale-grouped open coverings and use the maximal inequality to rule out a cover of too small $s$-cost for each $s<n$. Prove the ambient upper bound separately. Using only the compact three-dimensional formulation would not cover this domain or the other dimensions.

## Consequences
Specializing to $n=3$ gives the [three-dimensional Kakeya conclusion](wang-zahl-kakeya-dim-h.md) of Wang and Zahl.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L128-L132) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
