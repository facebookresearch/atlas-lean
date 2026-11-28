# Lower semicontinuity of a trace support weight

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

The support weight $s_\tau$ takes value zero where $\tau$ vanishes and $+\infty$ elsewhere on the positive cone. Write $Z_\tau=I_{s_\tau}$.

The function $s_\tau$ is lower semicontinuous on the positive cone.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Idea

Check all strict super-level sets, using lower semicontinuity of $\tau$ to show $\{\tau>0\}$ open.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, lowerSemicontinuous_supportWeight](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L134-L136).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
