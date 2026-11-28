# Sums preserve the finite square-trace domain

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

If $x,y\in D_\tau$, then $x+y\in D_\tau$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Idea

Prove monotonicity on the positive cone and use $(x+y)^*(x+y)\le2(x^*x+y^*y)$, then use additivity and finiteness.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, add_mem_finiteSquareSet](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L76-L78).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
