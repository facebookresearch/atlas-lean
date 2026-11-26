# Two limit cycles attained in the quintic Liénard model

There is a real polynomial $F$ of degree at most five such that $\dot x=y-F(x),\ \dot y=-x$ has exactly two limit cycles. These are distinct isolated images of nonconstant, globally defined solutions with positive periods; isolation is among whole periodic-orbit images contained in an open neighborhood of the cycle.

## Depends on
The planar solution and isolated-image definitions in the universal upper bound.

## Proof depends on
- [Quintic Liénard upper bound](quintic-lienard-at-most-two-limit-cycles.md), to exclude further cycles after a two-cycle construction.

## Proof strategy
Give a polynomial or parameter family and locate two distinct isolated periodic images by verified return-map crossings (or an equivalent construction). Rule out counting time shifts of one orbit twice.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QuinticLienard.lean#L39-L43) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/143.md).
