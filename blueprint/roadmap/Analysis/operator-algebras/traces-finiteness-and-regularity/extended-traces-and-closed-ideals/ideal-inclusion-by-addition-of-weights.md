# Ideal inclusion detected by addition of weights

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements.

For norm-closed two-sided star ideals $I,J$, $I\subseteq J$ if and only if $w_I+w_J=w_I$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Extended trace supported off a closed ideal](closed-ideal-weight-exists.md).

## Expansion

Compare positive zero sets of both traces and recover ideal inclusion from positive squares. Use the shared extended-valued trace model, not a finite positive functional.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, le_iff_add_weight](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L159-L160).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
