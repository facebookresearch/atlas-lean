# A nonzero quasinilpotent operator with a transitive commutant

On every separable infinite-dimensional complex Hilbert space $H$ there is a nonzero bounded operator $T$ with $\|T^n\|^{1/n}\to0$ as $n\to\infty$. Write $T'=\{A\in B(H):AT=TA\}$. This is a proper unital subalgebra, closed for pointwise norm convergence on $H$ (the strong operator topology), and if a closed complex linear subspace $K$ satisfies $AK\subset K$ for every $A\in T'$, then $K=0$ or $K=H$. The common-invariance conclusion is not about invariance under $T$ alone.

## Depends on

- The bounded operator commutant and the strong operator topology above.

## Proof depends on

- A nonzero quasinilpotent operator model with a transitive commutant, its strong closure and properness, and a transport of these properties across a unitary equivalence.

## Expansion

Isolate the weighted intertwiner construction and its orbit estimates before proving transitivity. Prove strong-operator closedness from continuity of left and right multiplication by a fixed operator, and treat properness separately. The companion comparators have the same operator conclusion and differ only in their derivations.

## Sources

- OpenAI, [BackwardIntertwiners comparator, direct_algebra_corollary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BackwardIntertwiners.lean#L36-L40).
- OpenAI, [HyperinvariantSubspaces comparator, main_theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HyperinvariantSubspaces.lean#L38-L40).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/293.md).
