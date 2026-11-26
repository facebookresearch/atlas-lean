# Vanishing of higher bounded Hochschild cohomology with self coefficients

Let $M$ be a complex von Neumann algebra (in the source, a $W^*$-algebra with the compatible star order), and $k\geq2$ an integer. A cochain is a complex bounded multilinear map $M^k\to M$. For an $m$-linear cochain $h$, use

$$
(dh)(x_0,\ldots,x_m)=x_0h(x_1,\ldots,x_m)+\sum_{j=0}^{m-1}(-1)^{j+1}h(x_0,\ldots,x_jx_{j+1},\ldots,x_m)+(-1)^{m+1}h(x_0,\ldots,x_{m-1})x_m.
$$

Every bounded $k$-linear $f$ satisfying $df=0$ pointwise has a bounded complex $(k-1)$-linear primitive $g$ with $dg=f$ pointwise. The norm continuity is ordinary bounded multilinearity, not an extra separate-normality assumption. The coefficient bimodule is $M$ itself.

## Depends on
The abstract $W^*$-algebra model, continuous multilinear cochains, and the signed Hochschild differential with both end actions.

## Proof depends on
A reduction or construction producing bounded primitives for ordinary bounded cocycles, not only separately ultraweakly continuous ones.

## Expansion
Verify the differential and its square-zero identity in every degree, separate any normal reduction from vanishing in the normal complex, and transport the primitive to the ordinary bounded complex with the exact self actions. No degree-one conclusion is included.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KadisonRingrose.lean#L30-L37) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/295.md).
