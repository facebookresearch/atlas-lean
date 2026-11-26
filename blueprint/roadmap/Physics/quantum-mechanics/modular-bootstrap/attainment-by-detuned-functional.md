# Attainment by the explicit detuned Fourier-odd functional

There is a charge cutoff $c_0^{\mathrm{att}}\ge40$, explicit in principle but not computed in the paper, such that for every $c\ge c_0^{\mathrm{att}}$ the [specific quantile-product function](explicit-attaining-functional.md) $g=(h_0-\widehat h_0)/2$ lies in $\overline{\mathcal A}$, has $g_{\mathrm{vac}}>0$, and satisfies $g(t)>0$ for **every** $t\ge t_\star+1$. Here $t_\star=c'\chi_2^2/3$ and

$$
t_\star=\xi_*c'+A_1(c')^{1/3}\bigl(1+O((c')^{-2/3})\bigr),\qquad
A_1=\frac23 x_*\kappa_{\mathrm{tip}}^{-2/3}\left(\frac74\right)^{2/3},\qquad
\kappa_{\mathrm{tip}}=\frac{4\,2^{3/4}}{9\sqrt\pi}.
$$

In particular $T_V(c)\le\xi_*c'+A_1(c')^{1/3}+O(1)$. The coefficient $A_1$ is about $0.483$; the formula, not the rounded decimal, is the coefficient of the stated bound. For each such $c$ there is a finite $C(c)$ such that at $t=c'x^2/3$ with $x\ge0$,

$$
|g(t)|\le C(c)e^{-c'L(x)}e^{-\pi x},\qquad L(x)=2\pi|x|/3.
$$

Both $h_0$ and its transform have faster decay than the inverse Cardy weight. This theorem gives a feasible cutoff, not a minimizing finite-$c$ functional or a sharp subleading constant. The paper's proof uses interval arithmetic for finitely many one-variable inequalities that are independent of $c$.

## Depends on

- [Exact detuned functional and threshold](explicit-attaining-functional.md)
- [Extremal potential and tip constants](strip-potential-and-zero-law.md)
- [Feasibility in the radial class](functional-class.md)
- [Best gap certificate](best-gap-certificate.md)

## Expansion

Derive the first kept site's expansion from the exact quantile $c'N(\chi_2)=7/4$. Establish the weighted decay and Fourier-odd property, compare the transformed function against the original on the full half-line from $t_\star+1$, and prove strict vacuum positivity after the second difference. Separate the $c$-uniform analytic estimates from the finite certified inequalities in Appendix H: each interval enclosure needs its own error and singular-endpoint control.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 5 and (7.5), p. 39](https://hexagonmath.org/pdf/2611.00174v1#page=39).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [tip coefficient (6.22), p. 34](https://hexagonmath.org/pdf/2611.00174v1#page=34).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Appendix H.1, interval certificates, p. 120](https://hexagonmath.org/pdf/2611.00174v1#page=120).
