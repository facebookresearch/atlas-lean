# Euclidean-complete affine maximal graphs in dimensions three through nine

For $3\le n\le9$ let $\Omega\subset\mathbb R^n$ be nonempty, open and convex, and let $u$ be smooth on $\Omega$ with positive-definite Hessian $H=D^2u$. Set $w=(\det H)^{-(n+1)/(n+2)}$ and $U=(\det H)H^{-1}$. Suppose $\sum_{i,j}U_{ij}\partial_i\partial_jw=0$ on $\Omega$. Require completeness of the intrinsic distance obtained by taking the infimum, over $C^1$ paths in $\Omega$ on $[0,1]$ with the given endpoints, of the length $\int_0^1\sqrt{\|\dot\gamma\|^2+(Du(\gamma)\dot\gamma)^2}\,dt$. Completeness means every Cauchy sequence for this distance converges in $\Omega$; it is not completeness in the affine metric.

Then $\Omega=\mathbb R^n$ and $u(x)=\tfrac12 x^TAx+b\cdot x+c$ for a real symmetric positive-definite matrix $A$, vector $b$, and scalar $c$. Some invertible affine map of $\mathbb R^{n+1}$ sends the standard graph $x\mapsto\|x\|^2$ onto the graph of $u$. The conclusion is about graphs, not all immersed hypersurfaces or the dimension-ten example.

## Depends on

- Coordinate Hessian, cofactor contraction, and the intrinsic Euclidean graph length above.

## Proof depends on

- Euclidean-complete graph domain extension and affine maximal rigidity estimates in the stated dimension interval.

## Expansion

Establish the path metric and compare single smooth paths with piecewise smooth paths via endpoint reparametrization. Isolate graph-domain extension and constancy of the Hessian as separate results, then integrate the constant Hessian and construct the affine map. Readiness requires the rigidity argument, not only a Hessian API.

## Sources

- OpenAI, [AffineBernstein comparator, affine_bernstein](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AffineBernstein.lean#L72-L89).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/353.md).
