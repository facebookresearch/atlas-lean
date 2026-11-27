# Bayesian phylodynamic inference

Model components of Bayesian phylodynamic software that infers time-scaled phylogenies jointly with trait evolution. Treating the sampling location of a taxon as a discrete character evolving along the phylogeny turns the reconstruction of spatial spread into ancestral state reconstruction under a continuous-time Markov chain. Because a location character provides a single site of data for many possible location pairs, the rate matrix is constrained by a sparsity prior on the migration graph or by a generalized linear model in covariates, with Bayes factors read off posterior inclusion probabilities. Conditional expectations of trait-change counts along branches date and count those changes, and marginal likelihood estimators compare models.

- [Discrete-trait continuous-time Markov chain model of phylogeographic diffusion](discrete-trait-ctmc-model-of-phylogeographic-diffusion.md)
- [Stochastic search variable selection over migration graphs](stochastic-search-variable-selection-over-migration-graphs.md)
- [Bayes factor test for an individual diffusion rate](bayes-factor-test-for-an-individual-diffusion-rate.md)
- [GLM parameterization of discrete phylogeographic diffusion](glm-parameterization-of-discrete-phylogeographic-diffusion.md)
- [Markov jump counts and rewards](markov-jump-counts-and-rewards.md)
- [Stepping-stone estimator of the marginal likelihood](stepping-stone-estimator-of-the-marginal-likelihood.md)
