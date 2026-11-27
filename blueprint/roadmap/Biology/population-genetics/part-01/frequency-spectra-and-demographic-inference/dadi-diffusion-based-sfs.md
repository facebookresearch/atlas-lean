# Finite-difference solution and grid extrapolation in diffusion-based spectrum inference (dadi)

The [expected joint site-frequency spectrum and its Poisson likelihood](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md) require the density of derived mutations, which solves the [multi-population diffusion](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md). Gutenkunst, Hernandez, Williamson and Bustamante (2009, Methods) compute it numerically: the forward diffusion equation is solved by a finite-difference scheme on a nonuniform grid, inspired by the method of Chang and Cooper (compare [conservative schemes for the forward equation](../../diffusion-theory/numerical-analysis-of-wright-fisher-equations/conservative-schemes-for-the-forward-equation.md)), and because new mutations enter at the first grid point rather than at frequency $1/(2N)$, each spectrum entry is extrapolated to an infinitely fine grid by a quadratic fit in its logarithm, computed from three grid sizes (Equation 5).

## Depends on

- [Multi-population diffusion for the joint allele-frequency density](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md)
- [Expected joint allele-frequency spectrum and its Poisson likelihood](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md)

## Expansion

1. The finite-difference discretization on a nonuniform grid, and its error.
2. The three-grid quadratic extrapolation in the logarithm of each entry (Equation 5), as an approximation stated separately from the exact model.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods (Numerics; Equation 5). <https://doi.org/10.1371/journal.pgen.1000695>
