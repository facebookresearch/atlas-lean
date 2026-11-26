# Additive trace transport carries ideal weights to ideal weights

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements. Given an additive bijection $F$ on the extended traces of $A$ and $B$, the induced ideal correspondence $\Phi$ sends $I$ to $I_{F(w_I)}$.

For every additive trace bijection $F$ and closed two-sided star ideal $I$, $w_{\Phi(I)}=F(w_I)$. No topology or homogeneity of $F$ is needed for this claim.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [The weight of a closed ideal is additively idempotent](closed-ideal-weight-is-idempotent.md).
- [Every additively idempotent extended trace is an ideal weight](idempotent-trace-is-ideal-weight.md).
- [The finite trace ideal of a closed ideal weight](finite-ideal-of-ideal-weight.md).

## Expansion

Transport additive idempotents, use their correspondence with closed ideals and verify both inverse identities. Use the shared extended-valued trace model, not a finite positive functional.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, closedIdealEquivOfAdditive_weight](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L193-L196).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
