# Latent temporal progression of tumor cohorts

Cancer transcriptomic cohorts are cross-sectional: each patient is sampled once. Ordering patients along a latent progression axis (a pseudotime) using expression similarity plus pathological stage turns the cohort into a pseudo time series, on which a progression-dependent dynamical model of gene regulation can be fitted. The ordering uses a diffusion-type random walk on a patient similarity graph summed over all walk lengths; the regulatory network is then estimated by sparse Bayesian regression on the reconstructed trajectory.

## Articles

- [Temporal progression distance from accumulated random walks](temporal-progression-distance-from-accumulated-random-walks.md)
- [Progression-dependent quadratic gene-regulation model and its Bayesian lasso fit](progression-dependent-quadratic-gene-regulation-model.md)
