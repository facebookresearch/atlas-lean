# Emission gain cross-section of a dye

The gain a dye can provide is estimated from quantities a screening laboratory already measures: the shape of its emission spectrum, its photoluminescence quantum yield, its fluorescence lifetime and the refractive index of the solvent.

Let an emitter in a medium of refractive index $n > 0$ have photoluminescence quantum yield $\phi \in [0,1]$ and fluorescence lifetime $\tau > 0$, and let its emission spectrum $I_{\mathrm{em}} \ge 0$ be a wavelength density with finite positive integral $\int I_{\mathrm{em}}(\lambda)\,\mathrm{d}\lambda$. With $c$ the speed of light in vacuum, the spectral gain factor and the emission gain cross-section at a wavelength $\lambda_{\max}$ of maximal emission intensity are

$$
f_{\mathrm{em}}(\lambda) = \frac{\lambda^{4} \cdot I_{\mathrm{em}}(\lambda)}{8 \pi c \cdot \int I_{\mathrm{em}}(\lambda)\, \mathrm{d}\lambda} ,
\qquad
\sigma_{\mathrm{em}}(\lambda_{\max}) = \frac{f_{\mathrm{em}}(\lambda_{\max}) \cdot \phi}{n^{2} \cdot \tau} .
$$

Hypotheses and conventions. The positive finite spectral integral is what makes $f_{\mathrm{em}}$ defined; a measured spectrum that is identically zero has no normalization, and then neither display applies. A maximizing wavelength must exist or be supplied as the measured peak, since integrability alone does not give one. The spectrum is a density per unit wavelength, so the factor $\lambda^{4}$ is tied to that variable and a wavenumber-resolved spectrum needs the corresponding change of variables. $\lambda_{\max}$ is a peak of the measured intensity, which is not in general a maximizer of $\lambda^{4}I_{\mathrm{em}}(\lambda)$. A non-emissive dye, with $\phi = 0$, gives a zero cross-section, and the quantity scales inversely with $n^{2}$ and with $\tau$, so a short-lived, high-yield, narrow-band emitter is favoured.

This is the laboratory metric the source stipulates for ranking candidates, not a derivation. A statement about stimulated emission would need an Einstein-coefficient lineshape model, and a claim about net gain in a device would need the loss terms as well, neither of which the measurement equation supplies.

## Depends on

- [Quantum yield of a photophysical process](quantum-yield-of-a-photophysical-process.md)
- [Lifetime of an excited state](excited-state-lifetime.md)

## Proof depends on

None.

## Expansion

A formal development takes a nonnegative integrable spectrum with positive integral on a wavelength interval, positive $n, \tau, c$, a yield in $[0,1]$ and a supplied peak wavelength, and defines $f_{\mathrm{em}}$ and $\sigma_{\mathrm{em}}$ by the displays. Two facts are worth recording: $f_{\mathrm{em}}$ is unchanged when $I_{\mathrm{em}}$ is multiplied by a positive constant, so only the spectral shape enters, and the dimensional check that $\sigma_{\mathrm{em}}$ has units of area when $I_{\mathrm{em}}$ is a density per unit wavelength.

## Context

Research-level, graduate prerequisites. The figure of merit by which Park, Mazaheri, Choi, Hao, Avagliano, Isbrandt, Karunathilaka, Adachi and Aspuru-Guzik rank candidate laser dyes in a self-driving laboratory, computed from solution-phase measurements before any device is built.

## Sources

- Hyun Suk Park, Mahdi Mazaheri, Changhyeok Choi, Han Hao, Davide Avagliano, Eric Isbrandt, Buddhika S. B. Karunathilaka, Chihaya Adachi and Alán Aspuru-Guzik, *Discovery of tunable and soluble organic emitters for solid-state lasers with a self-driving laboratory*, Nature Communications (2026), Methods, Eqs. 1–2. DOI [10.1038/s41467-026-69233-2](https://doi.org/10.1038/s41467-026-69233-2), PMC13032042.
