# Real part of the xi logarithmic derivative as a zeta zero sum

Use the entire Riemann xi normalization. For every $s$ with $\xi(s)\ne0$, the series in the following identity is absolutely convergent:

$$
\operatorname{Re}\frac{\xi'(s)}{\xi(s)}=\sum_{\rho}m_\rho\frac{\operatorname{Re}s-\operatorname{Re}\rho}{|s-\rho|^2}.
$$

Here $\rho$ ranges over **all** zeta zeros in the open strip, including both signs of the ordinate, with analytic multiplicity $m_\rho$. The zero set of $\xi$ agrees with this strip zero set, and the sum is not defined by a choice of good-height sequence.

## Depends on

- [Riemann xi function](riemann-xi.md)
- [Zero count with multiplicity](../zeros-of-the-riemann-zeta-function/count-with-multiplicity.md)

## Proof depends on

- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)
- [Riemann–von Mangoldt and unit-window bounds](../zeros-of-the-riemann-zeta-function/dyadic-riemann-von-mangoldt-and-local-count.md)
- [Functional equation of xi](riemann-xi-one-sub.md)

## Expansion

Prove agreement of zero sets and orders using the entire xi normalization. Use rectangles at good heights for the weighted argument-principle identity for the reflected log derivatives; control the boundary integrals, prove absolute convergence of the real terms, and reindex the reflected zeros. The generic contour theorem does not supply these boundary estimates.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/ExplicitFormula/ZeroFree.lean#L248-L288).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/ExplicitFormula/ZeroFree.lean#L1204-L1343).
