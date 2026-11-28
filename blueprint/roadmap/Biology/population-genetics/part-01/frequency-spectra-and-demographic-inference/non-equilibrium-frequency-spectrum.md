# Non-equilibrium allele frequency spectra

Evans, Shvets and Slatkin (2007) give a forward diffusion equation for the allele frequency spectrum $f(x, t)$, the density of derived alleles at frequency $x$ over independent loci, in a Wright–Fisher diffusion with or without selection and with relative population size $\rho(t)$. The influx of mutations enters through the boundary condition

$$\lim_{x \downarrow 0}xf(x, t) = \theta\rho(t)$$

(abstract and Section 3). When size and selection are constant the forward equation is equivalent to the backward diffusion usually used to derive the equilibrium spectrum, but it also gives the spectrum before equilibrium is reached and while size and selection vary. For a Wright–Fisher diffusion with constant selection and time-varying size (their Section 5) they derive a system of ordinary differential equations for the moments $\mu_n(t) = \int_0^1x^ng(x, t)\,dx$ of the weighted density $g$, obtained by integrating the forward equation by parts against $x^n$; Section 6 gives explicit recurrences for these moments in the neutral case with exponential population growth, and Section 7 expresses the expected spectrum of a sample of $n$ chromosomes in terms of them. They apply this to neutral and selected alleles in a simplified model of human history, finding, for example, that about $30\%$ of the expected heterozygosity of neutral loci is attributable to mutations that arose since the onset of population growth in roughly the last $150{,}000$ years (abstract).

## Depends on

- [ODE characterization of the Poisson random field density](../../diffusion-theory/poisson-random-field-model/eq-prf-density-of-forward.md)
- [Expected site frequency spectrum under variable population size](../../../coalescent-theory/site-frequency-spectrum-under-variable-populatio/variable-sfs.md)

## Expansion

1. The time-dependent density of derived alleles and its forward equation.
2. The influx boundary condition $\lim_{x \downarrow 0}xf(x, t) = \theta\rho(t)$, absorption at $1$, and the initial condition given by the previous equilibrium.
3. The moment equations for constant selection and varying size, and their explicit recurrences for the neutral diffusion with exponential growth.
4. The expected sample spectrum from the moments, and its agreement with the coalescent expected spectrum under variable size in the neutral case.

## Sources

- S. N. Evans, Y. Shvets and M. Slatkin, Non-equilibrium theory of the allele frequency spectrum, Theor. Popul. Biol. 71 (2007), 109–119, abstract and Sections 3, 5, 6 and 7. <https://doi.org/10.1016/j.tpb.2006.06.005>
