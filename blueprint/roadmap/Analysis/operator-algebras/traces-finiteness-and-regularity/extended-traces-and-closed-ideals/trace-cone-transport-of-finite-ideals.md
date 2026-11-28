# Trace-cone equivalence transports finite trace ideals

Use the notation of [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

For a norm-closed two-sided star ideal $I$, its weight $w_I$ takes the value zero on positive elements of $I$ and $+\infty$ on all other positive elements. Given an additive bijection $F$ on the extended traces of $A$ and $B$, the induced ideal correspondence $\Phi$ sends $I$ to $I_{F(w_I)}$. In the trace-cone equivalence hypotheses below, $F$ also preserves zero and positive scalar multiplication, and $F$ and $F^{-1}$ preserve the canonical filter convergence: for each $a\ge0$ and $\epsilon>0$, $\limsup \tau_i((a-\epsilon)_+)\le\tau(a)\le\liminf\tau_i(a)$. The cutoff is nonunital continuous functional calculus.

For every trace-cone equivalence $F$ and trace $\tau$, the order isomorphism $\Phi$ satisfies $\Phi(I_\tau)=I_{F(\tau)}$.

## Depends on

- [Extended traces and their finite square-trace domains](extended-trace-and-finite-domain.md).

## Proof depends on

- [Additive trace transport carries ideal weights to ideal weights](additive-transport-of-ideal-weights.md).
- [Ideal inclusion detected by addition of weights](ideal-inclusion-by-addition-of-weights.md).

## Expansion

Characterize $I_\tau$ in terms of its weight and the cone operations or canonical convergence, and compare the characterization on both sides of $F$. Use the shared extended-valued trace model, not a finite positive functional.

## Sources

- OpenAI, [TraceIdealTransportSupport comparator, idealOrderIso_finIdeal](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceIdealTransportSupport.lean#L225-L228).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/301.md).
