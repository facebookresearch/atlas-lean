# Poisson likelihood and numerical solution in diffusion-based spectrum inference (dadi)

Given the expected joint site-frequency spectrum $M(\Theta)$ of a demographic model with parameters $\Theta$, computed from the multi-population diffusion density and its binomial sampling map, Gutenkunst, Hernandez, Williamson and Bustamante (2009, Methods) treat each entry of the observed spectrum $S$ as an independent Poisson variable with mean $M(\Theta)$ when polymorphisms are unlinked, so the likelihood is the product of Poisson likelihoods over the entries (their Equation 4), maximized over $\Theta$; for linked polymorphisms the same product is a composite likelihood, and variances and critical values are obtained from coalescent simulations that include linkage. Numerically, the forward diffusion equation is solved by a finite-difference scheme on a nonuniform grid, inspired by the method of Chang and Cooper, and because new mutations enter at the first grid point rather than at frequency $1/(2N)$, each spectrum entry is extrapolated to an infinitely fine grid by a quadratic fit in its logarithm, computed from three grid sizes (Equation 5).

## Depends on

- [Joint site-frequency spectra of several populations](../../../Biology/population-genetics/frequency-spectra-and-demographic-inference/joint-multi-population-sfs.md)
- [Composition across demographic epochs, splits and admixture](../../../Biology/population-genetics/frequency-spectra-and-demographic-inference/piecewise-epochs-splits-and-admixture.md)
- [Site-frequency counts in the Poisson random field are independent Poisson](../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/independent-poisson-site-counts.md)

## Expansion

1. The product-of-Poisson likelihood of the observed joint spectrum for unlinked sites (Equation 4), and its status as a composite likelihood under linkage.
2. Estimation of variances and critical values for linked data by coalescent simulation.
3. The finite-difference discretization on a nonuniform grid, and its error.
4. The three-grid quadratic extrapolation in the logarithm of each entry (Equation 5), as an approximation stated separately from the exact model.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods (Likelihood-based inference; Numerics; Equations 4–5). <https://doi.org/10.1371/journal.pgen.1000695>
