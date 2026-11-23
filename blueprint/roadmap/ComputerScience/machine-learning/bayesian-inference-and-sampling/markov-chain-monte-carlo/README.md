# Markov chain Monte Carlo

- [Markov kernel of a transition rule](pmf-kernel.md)
- [Detailed balance implies reversibility](is-reversible-pmf-kernel.md)
- [Detailed balance implies invariance](invariant-pmf-kernel.md)
- [Detailed balance gives a stationary distribution](bind-eq-of-detailed-balance.md)
- [Metropolis–Hastings acceptance probability](mh-accept.md)
- [Metropolis–Hastings step](mh-step.md)
- [Detailed balance for Metropolis–Hastings](mh-detailed-balance.md)
- [The Metropolis–Hastings kernel is reversible](is-reversible-mh-kernel.md)
- [The target is stationary for Metropolis–Hastings](invariant-mh-kernel.md)
- [Normalizer of the conditional law](cond-norm.md)
- [Conditional law of a coordinate](cond-law.md)
- [Gibbs update](gibbs-step.md)
- [Symmetry of differing in one coordinate](update-eq-comm.md)
- [Detailed balance for a Gibbs update](gibbs-detailed-balance.md)
- [Gibbs updates are reversible](is-reversible-gibbs-kernel.md)
- [Gibbs sampling leaves the target stationary](invariant-gibbs-kernel.md)
- [Systematic-scan Gibbs sampler](gibbs-sweep.md)
- [First step of a Gibbs sweep](gibbs-sweep-cons-apply.md)
- [A full Gibbs sweep leaves the target stationary](invariant-gibbs-sweep.md)
- [Probabilities of a finite law sum to one](sum-to-real-pmf.md)
- [Metropolis–Hastings transition matrix](mh-matrix.md)
- [Metropolis–Hastings matrix is stochastic](mh-matrix-mem-row-stochastic.md)
- [Target is stationary for the Metropolis–Hastings matrix](vec-mul-mh-matrix.md)
- [Primitivity of the Metropolis–Hastings matrix](is-primitive-mh-matrix.md)
- [The Metropolis–Hastings chain converges to its target](exists-tv-dist-mh-matrix-pow-le.md)
- [Transition matrix of the systematic-scan Gibbs sweep](gibbs-sweep-matrix.md)
- [Gibbs sweep matrix is stochastic](gibbs-sweep-matrix-mem-row-stochastic.md)
- [Target is stationary for the Gibbs sweep matrix](vec-mul-gibbs-sweep-matrix.md)
- [Positivity of Gibbs sweep transition probabilities](gibbs-sweep-matrix-pos.md)
- [The systematic-scan Gibbs sampler converges to its target](exists-tv-dist-gibbs-sweep-matrix-pow-le.md)

## Related topics

- [Canonical paths and multicommodity flow](../../../../Probability/markov-chains/canonical-paths-and-multicommodity-flow/README.md): quantitative bounds on how fast a reversible chain approaches its target: canonical paths and flows bound the spectral gap, and fast mixing yields a low-congestion flow.
- [Langevin Monte Carlo](../langevin-monte-carlo/README.md): sampling from a density on $\mathbb{R}^p$ by noisy gradient steps, without accept/reject; for strongly log-concave targets it converges in $W_2$ up to a discretization bias.
- [Function-space MCMC](../../../../Probability/bayesian-statistics/function-space-mcmc/README.md): Metropolis–Hastings for posteriors with a Gaussian prior on a general state space, with proposals reversible for the prior such as preconditioned Crank–Nicolson.
