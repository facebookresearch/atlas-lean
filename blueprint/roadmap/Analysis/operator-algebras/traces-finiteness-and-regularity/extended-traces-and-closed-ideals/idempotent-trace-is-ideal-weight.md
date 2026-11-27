# Every additively idempotent extended trace is an ideal weight

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements.

If $\tau+\tau=\tau$, then $w_{I_\tau}=\tau$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Extended trace supported off a closed ideal](closed-ideal-weight-exists.md).
- [The norm-closed finite trace ideal is closed](finite-trace-ideal-is-closed.md).
- [Left multiplication preserves the closed finite trace ideal](left-multiply-in-finite-trace-ideal.md).
- [Right multiplication preserves the closed finite trace ideal](right-multiply-in-finite-trace-ideal.md).

## Expansion

An idempotent trace takes only zero or infinity. Identify its zero locus on positives using lower semicontinuity and positive square roots. Use the shared extended-valued trace model, not a finite positive functional.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, idempotent_eq_weight](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L164-L165).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
