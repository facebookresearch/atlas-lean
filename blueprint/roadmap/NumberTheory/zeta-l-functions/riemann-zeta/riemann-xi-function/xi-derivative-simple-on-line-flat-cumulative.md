# Simple xi-derivative zeros on the critical line: cumulative bound 0.85838

Let $I=(0,T]$ and let $Z(T)$ contain every zero $s$ of $\xi'$ with $\operatorname{Im}s\in I$, with **no restriction on $\operatorname{Re}s$** in the definition. Write $N(T)$ for the sum of the analytic orders of vanishing of $\xi'$ over $Z(T)$ (an infinite analytic order is sent to zero, and an infinite-support finite sum is zero in the totalized count). Let $M(T)$ count the points of $Z(T)$ of real part $1/2$ and analytic order exactly one. Then there is a real $T_0$ such that for every real $T\ge T_0$, $0.85838N(T)\le M(T)$. There is no additional $\varepsilon$ loss. The cardinality is the natural cardinality, totalized to zero on an infinite set.

## Depends on

- [Riemann xi function](riemann-xi.md)

## Proof depends on

- [Zeros of the xi derivative lie in the open critical strip](zeros-of-the-xi-derivative-in-the-open-critical-strip.md)
- [Dyadic and local counts for the xi derivative](xi-derivative-riemann-von-mangoldt.md)
- [Fixed-window bounds and strict decimal margins](xi-derivative-fixed-window-bounds-and-margin.md)

## Proof outline

Fix the parameter from the strict certificate for this profile. The numerator and denominator are additive on adjacent ordinate windows. Sum the unrounded dyadic estimate on the consecutive halves of $(0,T]$ down to its fixed threshold. The leftover initial interval lies in a fixed bounded positive-height window, so its denominator count is bounded; the derivative Riemann–von Mangoldt formula forces $N_1(0,T)\to\infty$. Choose the dyadic error and the eventual loss from the leftover interval within the strict margin above the stated decimal. Summing the bounds already rounded to the target decimal would not by itself give this exact cumulative coefficient.

## Sources

- Anthropic, [xiPrime_simple_zeros_on_critical_line_cumulative](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge/XiPrime.lean#L85-L90) (this page records one of the two bounds with the shared eventual threshold).
- [Interval additivity, denominator growth, and dyadic transfer](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Assembly.lean#L481-L549).
