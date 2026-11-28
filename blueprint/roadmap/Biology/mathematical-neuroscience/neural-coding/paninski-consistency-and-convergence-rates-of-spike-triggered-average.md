# Convergence rate of the spike-triggered average for Gaussian stimuli

Consider a probabilistic linear–nonlinear neuron whose spike probability $f$ depends on the stimulus $x$ only through its projection on an unknown filter subspace $K$, and i.i.d. stimuli with distribution $p$. Paninski (2003) proves the following for one-dimensional $K$, represented by a unit vector $k_1$ (so $K = \mathbb{R} k_1$ and $\|k_1\| = 1$; the scale below does not depend on which of the two unit vectors is chosen).

Consistency under elliptical symmetry and its necessity (Theorem 1) are stated as [consistency of the spike-triggered average](../consistency-of-the-spike-triggered-average/tendsto-spike-triggered-average.md) and [elliptical symmetry is necessary for consistency](../consistency-of-the-spike-triggered-average/exists-spike-triggered-average-not-paral.md). This page states the rate (Theorem 2). Suppose $p$ is symmetric normal with standard deviation $\sigma(p)$ in each coordinate and $m = E(\langle x, k_1\rangle \mid \text{spike}) \ne 0$. Let $\hat k$ be the spike-triggered average from $N_s$ spikes and measure its error by the tangent vector $e = P_{k_1^\perp} \hat k / \langle \hat k, k_1\rangle$ at $k_1$, where $P_{k_1^\perp}$ is the orthogonal projection onto $k_1^\perp$ (defined when $\langle \hat k, k_1\rangle \ne 0$, which holds with probability tending to one). Then the vector $\sqrt{N_s}\, e$ converges in law to the centered normal distribution on $k_1^\perp$ with covariance $(\sigma(p)/|m|)^2$ times the identity of $k_1^\perp$. The limit law is that of a vector; its length, the angular error, is not normal, and its typical size grows like $\sqrt{\dim X - 1}$.

He gives the corresponding consistency and rate results for spike-triggered covariance under Gaussian stimuli (Theorems 3 and 4) and a consistency result for an information-theoretic kernel estimator under general stimulus laws (Theorem 5).

## Depends on

- [Consistency of the spike-triggered average](../consistency-of-the-spike-triggered-average/tendsto-spike-triggered-average.md)

## Proof depends on

- [The spike-triggered average recovers the filter for spherically symmetric stimuli](spike-triggered-average-is-proportional-to-the-linear-filter-for-radia.md)

## Expansion

1. The model: the LN model with a one-dimensional filter, Gaussian stimuli, and the tangent error vector.
2. The central limit theorem for the tangent error vector $\sqrt{N_s}\, e$ and its asymptotic covariance, using that under the normal law the components of $x$ orthogonal to $k_1$ are independent of the spike given $\langle x, k_1\rangle$.
3. Spike-triggered covariance and the information-theoretic estimator, as separate statements.

## Sources

- L. Paninski, Convergence properties of three spike-triggered analysis techniques, Network: Comput. Neural Syst. 14 (2003), 437–464, Theorems 1–5. <https://doi.org/10.1088/0954-898x_14_3_304>
