# Log-concave Poisson count correction

Per-base read counts from ChIP-seq, DNase-seq and RNA-seq are far more overdispersed than the Poisson model assumed by most downstream tools, and no standard parametric mixture fits them. Modelling the latent log-rates nonparametrically as log-concave and then mapping counts quantile by quantile onto a Poisson distribution gives an assay-independent preprocessing step that generalizes read de-duplication.

- [Poisson log-concave compound model for read counts](poisson-log-concave-compound-model-for-read-counts.md)
- [Poissonization transform of overdispersed counts](poissonization-transform-of-overdispersed-counts.md)
