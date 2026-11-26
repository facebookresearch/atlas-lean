# Lower bound for distinct zeros of zeta in dyadic windows

Let $f=\zeta$ be the Riemann zeta
function.
For $I=(T,2T]$ let $N$ count the zeros of $f$ with $0\lt \operatorname{Re}z<1$
and $\operatorname{Im}z\in I$, counted with multiplicity. Let $M$ count distinct zeros
in this same set. For every $\varepsilon>0$ there is a real $T_0$ such that for all $T\ge T_0$,
$(5/6-\varepsilon)N\le M$.

## Depends on

- [Zeros in a window](window-zeros.md)
- [The open critical strip](open-critical-strip.md)
- [Count with multiplicity](count-with-multiplicity.md)

## Proof depends on

- [Dyadic and local zero count](dyadic-riemann-von-mangoldt-and-local-count.md)
- [Weil explicit formula](weil-explicit-formula-for-zeta.md)
- [Normalized window trace and Frobenius estimates](zeta-window-gram-moment-bounds.md)
- [Multiplicity-sensitive rank–trace certificate](zero-window-rank-trace-certificates.md)

## Proof outline

Apply the flat-window estimates and the limit as its parameter approaches one. Match the certificate to the displayed numerator, with the multiplicity-weighted denominator and signed ordinates. Do not infer the percentage from upper zero counts alone.

## Sources

- Levent Alpöge and Ralph Furman, [arXiv:2608.13637](https://arxiv.org/abs/2608.13637); Anthropic's [formalized statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge.lean#L151-L154).
