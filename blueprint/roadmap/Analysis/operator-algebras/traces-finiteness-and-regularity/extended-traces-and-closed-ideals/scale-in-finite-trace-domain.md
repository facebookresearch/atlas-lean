# Complex scalars preserve the finite square-trace domain

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

If $x\in D_\tau$ then $cx\in D_\tau$ for every $c\in\mathbb C$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Zero belongs to the finite square-trace domain](zero-in-finite-trace-domain.md).

## Idea

Split zero scalar from the positive scalar factor $|c|^2$ in the squared product and use homogeneity only in the positive case.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, smul_mem_finiteSquareSet](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L74-L75).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
