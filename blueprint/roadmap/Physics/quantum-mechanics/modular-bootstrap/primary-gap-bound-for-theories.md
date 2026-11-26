# The large-charge primary-gap bound for admissible theories

Let $c\ge c_0^{\mathrm{att}}\ge40$, with the cutoff of [the attainment theorem](attainment-by-detuned-functional.md), and write $c'=c-1$, $a=c'/12$. Use the [slit-strip constants](strip-potential-and-zero-law.md) $x_*=\operatorname{arsinh}(1)/\pi$ and $\kappa_{\mathrm{tip}}=4\,2^{3/4}/(9\sqrt\pi)$, and put $\xi_*=x_*^2/3$ and $\Lambda_V=(1/12+\xi_*)^{-1}$. The explicit functional of the attainment theorem is feasible at $t_\star+1$. For every admissible conformal field theory with this central charge,

$$
\Delta_1<a+t_\star+1
=\frac{c}{\Lambda_V}+A_1 c^{1/3}+O(1),
\qquad A_1=\frac23 x_*\kappa_{\mathrm{tip}}^{-2/3}\left(\frac74\right)^{2/3}.
$$

The strict inequality is to the exact certificate $a+t_\star+1$; the bounded remainder describes that cutoff as $c\to\infty$ and is independent of the theory. The result does not assert that there are theories attaining this bound, or that $A_1$ is optimal. The paper's computer-assisted label is inherited from attainment; the step from the functional to theories is by hand.

## Depends on

- [Admissible spectra and theory gap](admissible-spectrum.md)
- [Explicit attaining threshold](explicit-attaining-functional.md)
- [Slit-strip potential and tip constants](strip-potential-and-zero-law.md)

## Proof depends on

- [Certification from strict feasibility](certification-for-admissible-spectra.md)
- [Attainment with the exact subleading coefficient](attainment-by-detuned-functional.md)

## Proof outline

Apply certification to the attaining function at $T=t_\star+1>0$. The relative error $O((c')^{-2/3})$ in the subleading term contributes a bounded remainder. Combine the leading terms using $a+\xi_* c'=c'/\Lambda_V$; replacing $c'$ by $c$ in the linear and fractional terms changes only the bounded remainder.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [constants in Theorem 1, p. 14](https://hexagonmath.org/pdf/2611.00174v1#page=14), [tip coefficient in (6.22), p. 34](https://hexagonmath.org/pdf/2611.00174v1#page=34), and [Corollary 6 and (8.16), p. 56](https://hexagonmath.org/pdf/2611.00174v1#page=56).
