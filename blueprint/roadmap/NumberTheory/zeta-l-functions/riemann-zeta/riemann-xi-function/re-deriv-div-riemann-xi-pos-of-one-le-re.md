# Positivity of the real part of the xi logarithmic derivative

For all complex $s$
with $\operatorname{Re}s\ge1$, $\operatorname{Re}(\xi'(s)/\xi(s))>0$. Here $\xi(s)$ is
$s(s-1)\Lambda_0(s)/2+1/2$, with $\Lambda_0$ the entire completed zeta function with its
polar parts removed. Its denominator does not vanish in this half-plane.

## Depends on

- [Riemann xi function](riemann-xi.md)

## Proof depends on

- [Real logarithmic derivative zero sum](real-part-of-the-xi-logarithmic-derivative-zero-sum.md)
- [Riemann xi nonvanishing for real part at least one](riemann-xi-ne-zero-of-one-le-re.md)
- [A nonempty zero window for large heights](../zeros-of-the-riemann-zeta-function/dyadic-riemann-von-mangoldt-and-local-count.md)

## Proof outline

Use the real-part sum for the normalized xi function, the nonvanishing denominator on this half-plane, and existence of a zeta strip zero from the dyadic count. Each term is positive once its multiplicity is positive; its real-part difference is strictly positive even on the boundary $\operatorname{Re}s=1$.

## Sources

- Anthropic's [formalized statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Challenge/XiPrime.lean#L71-L74).
