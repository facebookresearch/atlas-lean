# Distinct xi-derivative zeros: dyadic bound 0.92919

Let $I=(T,2T]$ and let $Z(T)$ contain every zero $s$ of $\xi'$ with $\operatorname{Im}s\in I$, with **no restriction on $\operatorname{Re}s$** in the definition. Write $N(T)$ for the sum of the analytic orders of vanishing of $\xi'$ over $Z(T)$ (an infinite analytic order is sent to zero, and an infinite-support finite sum is zero in the totalized count). Let $M(T)$ be the number of distinct points of $Z(T)$, with each point counted once. Then there is a real $T_0$ such that for every real $T\ge T_0$, $0.92919N(T)\le M(T)$. There is no additional $\varepsilon$ loss. The cardinality is the natural cardinality, totalized to zero on an infinite set.

## Depends on

- [Riemann xi function](riemann-xi.md)

## Proof depends on

- [Zeros of the xi derivative lie in the open critical strip](zeros-of-the-xi-derivative-in-the-open-critical-strip.md)
- [Dyadic and local counts for the xi derivative](xi-derivative-riemann-von-mangoldt.md)
- [Fixed-window bounds and strict decimal margins](xi-derivative-fixed-window-bounds-and-margin.md)

## Proof outline

Fix a parameter from the strict certificate for this profile; take the error in the fixed-parameter bound smaller than the margin above the stated decimal. This yields the displayed coefficient on all sufficiently large dyadic windows, without changing which zeros enter the count.

## Sources

- Anthropic, [xiPrime_simple_zeros_on_critical_line](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge/XiPrime.lean#L76-L83) (this page records one of the two bounds with the shared eventual threshold).
