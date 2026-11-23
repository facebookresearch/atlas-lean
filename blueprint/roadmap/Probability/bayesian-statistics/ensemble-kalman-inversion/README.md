# Ensemble Kalman inversion

Ensemble Kalman inversion solves an inverse problem $y = G(u) + \eta$ derivative-free, by moving an ensemble of $J$ particles with the Kalman update built from empirical covariances, $u^{(j)} \mapsto u^{(j)} + C^{up}(C^{pp} + \Gamma)^{-1}(y^{(j)} - G(u^{(j)}))$. Every iterate stays in the linear span of the initial ensemble. Except for linear Gaussian problems the ensemble does not approximate the posterior as $J \to \infty$, so Schillings and Stuart analyse the method for fixed $J$ as an optimiser on that subspace: in the continuous-time limit for a linear forward map it is a gradient flow of the misfit preconditioned by the empirical covariance, and the ensemble collapses onto its mean.

- [Ensemble mean](ensemble-mean.md)
- [EKI cross-covariance applied to a vector](cross-cov.md)
- [EKI output covariance](output-cov.md)
- [One step of ensemble Kalman inversion](eki-step.md)
- [The ensemble mean stays in a subspace](ensemble-mean-mem.md)
- [The cross-covariance stays in the ensemble's subspace](cross-cov-mem.md)
- [One EKI step preserves every subspace containing the ensemble](eki-step-mem.md)
- [Invariant subspace property of ensemble Kalman inversion](eki-mem-span.md)
- [The EKI estimate cannot beat the best approximation from the initial span](inf-dist-le-dist-ensemble-mean.md)
- [Ensemble collapse for continuous-time ensemble Kalman inversion](eki-ensemble-collapse.md)

## Related topics

- [Kalman filter](../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/README.md): the exact linear-Gaussian update that the ensemble update imitates with empirical covariances.
- [Gaussian conditioning](../../distributions/continuous/gaussian-conditioning/README.md): the conditioning formula behind the Kalman gain $C^{up}(C^{pp} + \Gamma)^{-1}$.
- [Bayesian inverse problems](../bayesian-inverse-problems/README.md): the inverse problems the method addresses, and their posteriors.
