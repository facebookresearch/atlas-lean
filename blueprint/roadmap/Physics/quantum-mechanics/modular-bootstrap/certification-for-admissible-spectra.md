# A feasible functional certifies a primary below its threshold

Let $c\ge40$ and let $g\in\overline{\mathcal A}$ be feasible at a real $T>0$: $g(t)\ge0$ for $t\ge T$ and $g_{\mathrm{vac}}>0$. Every [admissible spectrum](admissible-spectrum.md) at this charge has a primary at $t_n<T$, possibly with $t_n<0$. Consequently every admissible theory satisfies $\Delta_1\le T_V(c)+a=\Delta_1^{\mathrm{best}}(c)$. The witnessed bound with $T$ is strict; the bound using the infimum need not be.

The hypothesis needs no smoothness or faster decay of $g$ beyond that defining $\overline{\mathcal A}$. Weak feasibility with zero vacuum action alone does not certify a strict gap exclusion. The paper proves certification by hand.

## Depends on

- [Admissible spectra and gap](admissible-spectrum.md)
- [Functional class and strict feasibility](functional-class.md)
- [Best gap certificate](best-gap-certificate.md)

## Expansion

Do not assume termwise application of an arbitrary functional to the crossing sum. In the countercase where all primaries satisfy $t_n\ge T$, first prove the regularized sum identity with the positive Abel–Laguerre kernel and vanishing even Fourier coefficients. Control the Cardy-weighted limit on the continuum, and show that the contribution from the negative part below $T$ vanishes in the spectral tail. Fatou's lemma then forces the nonnegative spectral sum to be at most $-g_{\mathrm{vac}}<0$. Finally approximate the strict feasibility infimum without assuming an extremizer.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 2, p. 14](https://hexagonmath.org/pdf/2611.00174v1#page=14).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§8.3, Fatou bound (8.15), p. 55](https://hexagonmath.org/pdf/2611.00174v1#page=55).
