# Logarithmic Brunn–Minkowski inequality for origin-symmetric convex bodies

For each integer $n\ge1$, let $K,L\subset\mathbb R^n$ be convex bodies invariant under $x\mapsto-x$. For $0\le t\le1$ let $h_K(u)=\sup_{x\in K}\langle x,u\rangle$ and define $W=\{x:\langle x,u\rangle\le h_K(u)^{1-t}h_L(u)^t\text{ for all }\|u\|=1\}$. Then $|K|^{1-t}|L|^t\le |W|$, with volume considered in the extended nonnegative reals and exponents real. The endpoints $0,1$ are included. There are no boundary-smoothness or unconditionality assumptions.

## Depends on

- [Convex body](../../packings-and-coverings/hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Support functions and logarithmic Wulff half-space interpolation.

## Proof depends on

- Derive the intended unrestricted logarithmic volume inequality, not ordinary Minkowski-addition Brunn–Minkowski.

## Expansion

Prove positivity of the support functions on the unit sphere, establish the Wulff-body conventions and verify the two endpoint equalities. Break out the interior-$t$ inequality following the source proof.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LogBrunnMinkowski.lean#L30-L36) (statement and local definitions).
