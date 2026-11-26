# Maximal triangular Hilbert transform at the symmetric exponents

For complex $F,G\in L^3(\mathbb R^2)$ put $h_{x,y}(t)=F(x+t,y)G(x,y+t)/t$. A point is good if $h_{x,y}$ is Lebesgue integrable on $\{t:1/(n+2)<|t|<n+2\}$ for every integer $n\geq0$. At good points set $M(F,G)(x,y)=\sup_{0<\epsilon<R<\infty}|\int_{\epsilon<|t|<R}h_{x,y}(t)\,dt|$ as an extended nonnegative value, and set it to zero at other points. Good points have full measure, $M(F,G)$ is almost everywhere measurable, and $(\int M(F,G)^{3/2})^{2/3}\leq C\|F\|_3\|G\|_3$ for one nonnegative constant $C$ independent of the inputs. Both truncation endpoints vary.

## Depends on

Product Lebesgue measure, finite annulus integrals, and the supremum over all real pairs of ordered positive cutoffs.

## Proof depends on

Almost-everywhere joint annular integrability and the uniform maximal estimate for the trilinear geometry of the two shifts.

## Expansion

Use countable annular exhaustion for the common good set. Justify cutoff continuity there so measurable rational cutoffs compute the same supremum; then connect the symmetric $L^3 \times L^3$ estimate to the extended $L^{3/2}$ norm. This endpoint does not assert a variation bound.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TriangularHilbert.lean#L50-L52) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/082.md).
