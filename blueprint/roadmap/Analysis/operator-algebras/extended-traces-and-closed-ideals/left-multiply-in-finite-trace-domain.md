# Left multiplication preserves the finite square-trace domain

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

If $y\in D_\tau$ and $x\in A$, then $xy\in D_\tau$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Idea

Use $y^*x^*xy\le\|x\|^2 y^*y$, monotonicity and the zero/nonzero scalar cases.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, mul_mem_finiteSquareSet_left](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L79-L81).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
