# Dyadic Riemann–von Mangoldt formula and local zeta zero count

Count zeros with multiplicity, using the open critical strip and signed ordinate windows $(a,b]$. The two estimates needed by the zero-proportion argument are

$$
N(T,2T)=\frac{T}{2\pi}\left(\log\frac{T}{2\pi}+2\log2-1\right)+O(\log T)\quad(T\to+\infty)
$$

and $N(t,t+1)\le A\log(|t|+3)$ for **all** real $t$ and some $A\ge1$. In the first estimate the bound holds eventually for all real $T$, not only ordinates avoiding zeros.

## Depends on

- [Zeros in a window](window-zeros.md)
- [The open critical strip](open-critical-strip.md)
- [Count with multiplicity](count-with-multiplicity.md)

## Proof depends on

- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)

## Expansion

First prove the folded contour identity for endpoints avoiding zeros. Evaluate the gamma term by vertical Stirling estimates and bound the horizontal zeta term by Backlund’s estimate. Use the local unit-window bound to pass to arbitrary half-open boundaries, including zero ordinates at either endpoint.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Hypotheses.lean#L57-L70).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/RvM/MainTerm.lean#L12-L43).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/RvM/Statement.lean#L15-L22).
