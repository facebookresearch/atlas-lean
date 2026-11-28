# Hanner equality characterization for the symmetric Mahler product

For $n\geq1$ and a compact convex origin-symmetric $K\subseteq\mathbb R^n$ with nonempty interior, write $K^\circ=\{y:y\cdot x\leq1\text{ for every }x\in K\}$. Then $|K|\,|K^\circ|=4^n/n!$ if and only if $K$ is the image by an invertible real linear map of a body recursively built as follows: start with intervals $[-a,a]$ with $a>0$, and take products $A\times B$ or convex hulls of $(A\times\{0\})\cup(\{0\}\times B)$ in the combined coordinates.

## Depends on
- [Hanner polytope](is-hanner-polytope.md), whose unit-segment and linear-equivalence closure must be compared to the source's interval and outer-linear-image convention.
- [Polar set](../../../Analysis/convex-analysis-and-variations/polar-sets/polar-set.md).

## Proof depends on

- [Sharp symmetric Mahler bound](../extremal-volume-and-area-bounds/symmetric-mahler-sharp-bound.md).

The equality-case passage to metric medians in the gauge space of the body and its dual, and the recursive linear Hanner classification from these properties.

## Expansion

Prove the metric-median implication at equality and the resulting decomposition, with induction on dimension. Separately evaluate Hanner volume products using polarity interchanging products and joins, and verify the equivalence of the interval convention with the usual unit-segment convention up to invertible linear maps.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SymmetricMahlerEquality.lean#L43-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/087.md).
