# Zeros of the xi derivative lie in the open critical strip

For every complex $s$ such that $\xi'(s)=0$, one has $0<\operatorname{Re}s<1$. Here $\xi$ is the entire Riemann xi function in the normalization $\xi(s)=s(s-1)\Lambda_0(s)/2+1/2$. The statement concerns **all** complex zeros of its derivative, not just the zeros assumed to lie in the strip and not the zeros of $\xi$ itself.

## Depends on

- [Riemann xi function](riemann-xi.md)

## Proof depends on

- [Positive real part of the xi logarithmic derivative](re-deriv-div-riemann-xi-pos-of-one-le-re.md)
- [Functional equation of the Riemann xi function](riemann-xi-one-sub.md)

## Proof outline

Use nonvanishing of the logarithmic derivative in the closed right half-plane and differentiate the functional equation to obtain nonvanishing in the closed left half-plane.

## Sources

- Anthropic, [xiPrime_zeros_in_open_critical_strip](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge/XiPrime.lean#L66-L69).
