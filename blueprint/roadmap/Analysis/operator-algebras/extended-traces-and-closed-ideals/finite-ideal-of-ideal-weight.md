# The finite trace ideal of a closed ideal weight

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements.

For every norm-closed two-sided star ideal $I$, $I_{w_I}=I$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Extended trace supported off a closed ideal](closed-ideal-weight-exists.md).

## Expansion

Use $x^*x\in I\iff x\in I$ from the C*-quotient norm, then use closedness of $I$. Use the shared extended-valued trace model, not a finite positive functional.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, finiteIdeal_weight](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L158-L158).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
