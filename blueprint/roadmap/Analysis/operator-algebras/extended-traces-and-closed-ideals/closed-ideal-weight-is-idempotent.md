# The weight of a closed ideal is additively idempotent

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements.

For every norm-closed two-sided star ideal $I$, $w_I+w_I=w_I$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Extended trace supported off a closed ideal](closed-ideal-weight-exists.md).

## Idea

Use pointwise addition. At a positive element of $I$ the equality is $0+0=0$; at a positive element outside $I$ it is $+\infty+(+\infty)=+\infty$.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, weight_idempotent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L157-L157).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
