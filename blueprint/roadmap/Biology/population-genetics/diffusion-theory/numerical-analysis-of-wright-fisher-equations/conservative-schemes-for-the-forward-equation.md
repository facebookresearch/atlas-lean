# Conservative schemes for the forward equation

This page covers a research target: an explicit grid scheme for the forward equation of the Wright–Fisher diffusion with proofs that it preserves nonnegativity, that it conserves total mass including the mass absorbed at the endpoints, and that it treats the influx of new mutations correctly. A numerical plot is not a proof of these properties.

## Expansion

Fix the scheme and the treatment of the endpoints and of mutation influx, then state and prove nonnegativity and conservation, each as a page of its own.

Prerequisites:

- [Wright's stationary density solves the zero-flux equation](../wright-fisher-diffusion/deriv-flux-wright-density.md)

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, *PLoS Genet.* 5 (2009), e1000695, <https://doi.org/10.1371/journal.pgen.1000695> (a grid scheme for the forward equation).
- T. Maruyama, *Stochastic Problems in Population Genetics*, Lecture Notes in Biomathematics 17, Springer (1977), <https://doi.org/10.1007/978-3-642-93065-2>.
