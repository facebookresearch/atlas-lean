# Gaussian process inference of population size trajectories

The coalescent times of a genealogy sampled from a population of varying effective size form a point process whose conditional intensity is the number of lineage pairs divided by the effective population size. Estimating the size trajectory is therefore an intensity-estimation problem: coalescent times can be simulated by thinning a constant-rate process, and recording the thinned points makes the likelihood under a sigmoidal Gaussian process prior tractable for Markov chain Monte Carlo.

- [Coalescent point process and thinning simulation](coalescent-point-process-and-thinning-simulation.md)
- [Sigmoidal Gaussian process prior and thinning-augmented coalescent likelihood](sigmoidal-gaussian-process-prior-and-thinning-augmented-coalescent-likelihood.md)
