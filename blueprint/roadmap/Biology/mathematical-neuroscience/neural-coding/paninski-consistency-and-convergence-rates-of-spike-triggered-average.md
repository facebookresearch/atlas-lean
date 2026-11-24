# Consistency of spike-triggered analysis for symmetric stimuli

Consider a probabilistic linear–nonlinear neuron whose spike probability $f$ depends on the stimulus $x$ only through its projection on an unknown filter subspace $K$, and i.i.d. stimuli with distribution $p$. Paninski (2003) proves the following for one-dimensional $K$ spanned by $k_1$.

1. Consistency (Theorem 1). If $p$ is radially symmetric and $E(\langle x, k_1\rangle \mid \text{spike}) \ne 0$, the spike-triggered average is a consistent estimator of the direction $k_1$; if $p(A^{1/2} x)$ is radially symmetric, the same holds for the spike-triggered average after whitening by the stimulus covariance. Conversely, if $p$ is radially symmetric and $E(\langle x, k_1\rangle \mid \text{spike}) = 0$, the estimator has positive asymptotic bias, and if $p$ is not radially symmetric, there is a nonlinearity $f$ for which it is asymptotically biased.
2. Rate (Theorem 2). If $p$ is symmetric normal with standard deviation $\sigma(p)$ and the estimator is consistent, then $\sqrt{N_s}$ times its error is asymptotically normal with mean zero and scale $\sigma(p)/|E(\langle x, k_1\rangle \mid \text{spike})|$, where $N_s$ is the number of spikes, so the asymptotic error grows like $\sqrt{\dim X - 1}$.

He gives the corresponding consistency and rate results for spike-triggered covariance under Gaussian stimuli (Theorems 3 and 4) and a consistency result for an information-theoretic kernel estimator under general stimulus laws (Theorem 5).

## Proof depends on

- [The spike-triggered average recovers the filter for spherically symmetric stimuli](spike-triggered-average-is-proportional-to-the-linear-filter-for-radia.md)

## Expansion

1. The model: the LN model with a low-dimensional filter subspace, the stimulus distribution, and the estimators, with the error measured on the Grassmannian.
2. The population identity under radial symmetry (the [spike-triggered average proportionality](spike-triggered-average-is-proportional-to-the-linear-filter-for-radia.md)) and the law of large numbers for the empirical spike-triggered average.
3. The converse: a distribution is radially symmetric if and only if the conditional mean of $x$ vanishes on all planar slices, by characteristic functions.
4. The central limit theorem for the estimator and its asymptotic covariance, including the whitened estimator under elliptical symmetry.
5. Spike-triggered covariance and the information-theoretic estimator, as separate statements.

## Sources

- L. Paninski, Convergence properties of three spike-triggered analysis techniques, Network: Comput. Neural Syst. 14 (2003), 437–464, Theorems 1–5. <https://doi.org/10.1088/0954-898x_14_3_304>
