# Montgomery–Taylor bound for simple zeros on the critical line of zeta in cumulative windows

**Montgomery–Taylor bound for simple zeros on the critical line of zeta in cumulative
windows.** Let $f=\zeta$ be the Riemann zeta function.
For $I=(0,T]$ let $N$ count the zeros of $f$ with $0\lt \operatorname{Re}z<1$
and $\operatorname{Im}z\in I$, counted with multiplicity. Let $M$ count simple zeros on the
critical line
in this same set (simple means order exactly one, and the line is $\operatorname{Re}z=1/2$). For
every $\varepsilon>0$ there is a real $T_0$ such that for all $T\ge T_0$,
$(2-1/c_*-\varepsilon)N\le M$. The Montgomery–Taylor window constant is
$c_* = \sqrt{2}\tan(1/\sqrt{2})/(1+\tan(1/\sqrt{2})/\sqrt{2})$.

## Depends on

- [Zeros in a window](window-zeros.md)
- [The open critical strip](open-critical-strip.md)
- [Count with multiplicity](count-with-multiplicity.md)
- [Simple distinct points on the line](count-simple-on-line.md)
- [Montgomery–Taylor window constant](montgomery-taylor-window-constant.md)

## Proof depends on

- [The corresponding dyadic inequality](montgomery-taylor-simple-zeta-zeros-on-c.md)
- [Dyadic zero count and unit-window control](dyadic-riemann-von-mangoldt-and-local-count.md)

## Proof outline

Sum the dyadic bounds above a fixed cutoff. Bound the omitted low-ordinate contribution and show it is negligible relative to the cumulative count, keeping the half-open endpoints and the exact epsilon loss.

## Sources

- Levent Alpöge and Ralph Furman, [arXiv:2608.13637](https://arxiv.org/abs/2608.13637); Anthropic's [formalized statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge.lean#L173-L176).
