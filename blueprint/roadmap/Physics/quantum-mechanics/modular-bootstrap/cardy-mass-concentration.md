# Exponential Cardy-weighted mass concentration

Let $x_*=\operatorname{arsinh}(1)/\pi$. For every $0<\delta<x_*$ there is a finite constant $C_\delta$ such that for all $c\ge40$ and all $g\in\overline{\mathcal A}$,

$$
\int_0^{c'(x_*-\delta)^2/3}|g(t)|V(t)\,dt
\le C_\delta\,(c')^4 e^{-\kappa(\delta)c'}\,M[g].
$$

No feasibility or sign hypothesis on $g$ is imposed. Here $\kappa(\delta)$ is the explicit positive [Cardy deficit](strip-potential-and-zero-law.md). With an absolute constant $C_{\mathrm{conc}}$ one may take $C_\delta\le C_{\mathrm{conc}}\delta^{-5}$. The deficit satisfies

$$
\kappa(\delta)=\frac89\sqrt{2\sqrt2\,\pi}\,\delta^{3/2}(1+O(\delta))\quad(\delta\downarrow0),
\qquad \kappa(\delta)\ge\frac89\sqrt{2\pi}\,\delta^{3/2}\ge 2.228\,\delta^{3/2}\quad(0<\delta\le x_*).
$$

The concentration theorem is by hand. The endpoint $\delta=x_*$ in the deficit inequality does not enlarge the stated range of the mass estimate.

## Depends on

- [Admissible functional class](functional-class.md)
- [Cardy weight and absolute mass](cardy-weight.md)
- [Slit-strip potential and deficit](strip-potential-and-zero-law.md)

## Expansion

Continue the radial kernel to the fixed strip in $b=\sqrt{3t/c'}$ with controlled edge growth. Prove the slit-strip harmonic majorant using the Cardy bounds and weighted mass, retain the $\delta^{-5}(c')^3$ bound on the interior, and integrate the weighted prefactor over $0\le t\le c'(x_*-\delta)^2/3$ to account for the fourth power of $c'$. Treat $g=0$ directly rather than dividing by a zero mass.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 3 and (6.1), pp. 26–27](https://hexagonmath.org/pdf/2611.00174v1#page=26).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [deficit constants and (6.2), p. 27](https://hexagonmath.org/pdf/2611.00174v1#page=27).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Lemma 6.7 and proof, p. 35](https://hexagonmath.org/pdf/2611.00174v1#page=35).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [exact lower constant (C.17), p. 90](https://hexagonmath.org/pdf/2611.00174v1#page=90).
