# The optimal asymptotic slope of the spinless modular certificate

Let $c\to+\infty$ through real central charges $c\ge40$ and $c'=c-1$. Put

$$
x_*=\frac{\operatorname{arsinh}(1)}{\pi},\qquad
\xi_*=\frac{x_*^2}{3},\qquad
\Lambda_V=\frac{1}{1/12+\xi_*}=\frac{12\pi^2}{\pi^2+4\operatorname{arsinh}^2(1)}.
$$

For the [best strictly feasible certificate](best-gap-certificate.md), the paper's slope theorem states

$$
\lim_{c\to\infty}\frac{T_V(c)}{c'}=\xi_*,
\qquad\text{equivalently}\qquad
\lim_{c\to\infty}\frac{c}{\Delta_1^{\mathrm{best}}(c)}=\Lambda_V.
$$

The equivalence uses $\Delta_1^{\mathrm{best}}=T_V+c'/12$, eventual finiteness, and $c/c'\to1$. The slope is an optimum for the designated certificate class, not evidence that any theory saturates a gap bound. The paper labels this theorem computer-assisted because its specific attainment proof uses the interval inequalities of Appendix H; the lower bound is by hand.

## Depends on

- [Best Virasoro gap certificate](best-gap-certificate.md)

## Proof depends on

- [Lower limit on weakly feasible functionals](optimality-of-gap-certificates.md)
- [Explicit attaining functional estimate](attainment-by-detuned-functional.md)

## Proof outline

For sufficiently large $c$, strict feasibility implies weak feasibility for a nonzero function, so the uniform lower estimate bounds the infimum. The explicit feasible function bounds the infimum from above. Dividing by $c'$ sends both error terms to zero, and the shifted limit is positive, so taking its reciprocal gives the stated slope.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 1 and (2.21), p. 14](https://hexagonmath.org/pdf/2611.00174v1#page=14).
