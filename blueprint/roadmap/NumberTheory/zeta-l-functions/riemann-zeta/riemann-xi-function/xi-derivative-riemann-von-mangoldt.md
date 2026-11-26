# Dyadic Riemann–von Mangoldt formula and local counts for the xi derivative

Let $N_1(a,b)$ be the sum of the analytic multiplicities of all zeros of $\xi'$ with ordinate in $(a,b]$, with no real-part restriction in its definition. There are $C,T_0\in\mathbb R$ such that for every $T\ge T_0$,

$$
\left|N_1(T,2T)-\frac{T}{2\pi}\left(\log\frac{T}{2\pi}+2\log 2-1\right)\right|\le C\log T.
$$

There is an $A\ge1$ with $N_1(t,t+1)\le A\log(|t|+3)$ for every real $t$. These are bounds for the derivative, not for $\xi$ or $\zeta$.

## Depends on

- [Riemann xi function](riemann-xi.md)
- [Count with multiplicity](../zeros-of-the-riemann-zeta-function/count-with-multiplicity.md)

## Proof depends on

- [Zeros of the xi derivative lie in the open critical strip](zeros-of-the-xi-derivative-in-the-open-critical-strip.md)
- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)

## Expansion

Prove that $\xi'$ is not identically zero and obtain isolation and finite multiplicity, using the strip result for bounded-height compactness. Obtain good heights and fold the argument-principle integral of $\xi''/\xi'$ by the derivative's reflection symmetries. On the right half of the contour subtract the real gamma-factor logarithmic derivative and bound the contribution of the remaining logarithmic derivative by $O(\log T)$. Combine the asymptotic gamma term with the local bound in both signs of the ordinate to pass from good heights to arbitrary half-open endpoints.

## Sources

- [Derivative zero configuration and Riemann–von Mangoldt input](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Final.lean#L80-L91)
- [Folded derivative count and main term](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/ZeroCount.lean#L146-L171)
- [Shape of the dyadic and local estimates](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/RvM/Defs.lean#L9-L24)
