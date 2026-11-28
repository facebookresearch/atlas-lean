# Sigmoidal Gaussian process prior and thinning-augmented coalescent likelihood

Model the effective population size trajectory of an isochronously sampled genealogy with coalescent times $0 = t_n < t_{n-1} < \cdots < t_1$ by

$$
N_e(t) = \left[\frac{\lambda}{1 + e^{-f(t)}}\right]^{-1}, \qquad f \sim \mathcal{GP}\bigl(0, C_\theta\bigr),
$$

so that a priori $1/N_e(t)$ is a sigmoidal Gaussian process with values in $(0,\lambda)$, and $1/\lambda$ is a lower bound on $N_e$. The coalescent likelihood

$$
P(\mathcal{T} \mid \lambda, f) = \prod_{k=2}^{n} \frac{C_k\lambda}{1 + e^{-f(t_{k-1})}} \exp\left[-C_k \int_{t_k}^{t_{k-1}} \frac{\lambda}{1 + e^{-f(u)}}\,du\right], \qquad C_k = \binom{k}{2},
$$

involves an integral of the infinite-dimensional random function $f$, and the posterior is doubly intractable. Augment the observed times $\mathcal{T}$ with the points $\mathcal{N}_k = \{t_{k,1},\dots,t_{k,m_k}\} \subset (t_k, t_{k-1})$ rejected when the coalescent is simulated by thinning a rate-$C_k\lambda$ Poisson process with acceptance probability $1/(1 + e^{-f(t)})$. The augmented likelihood is

$$
P(t_{k-1}, \mathcal{N}_k \mid t_k, f, \lambda) = (C_k\lambda)^{m_k+1}\, e^{-C_k\lambda (t_{k-1} - t_k)}\, \frac{1}{1 + e^{-f(t_{k-1})}} \prod_{i=1}^{m_k} \left[1 - \frac{1}{1 + e^{-f(t_{k,i})}}\right],
$$

and $P(\mathcal{T},\mathcal{N} \mid f,\lambda) = \prod_{k=2}^n P(t_{k-1},\mathcal{N}_k \mid t_k, f, \lambda)$ depends on $f$ only through its values at the finitely many observed and latent times; integrating out the latent points recovers $P(\mathcal{T} \mid \lambda, f)$. The posterior of $f$ at those times, $\lambda$ and $\theta$ is then proportional to this augmented likelihood times a finite-dimensional Gaussian prior, and can be sampled by Markov chain Monte Carlo (Metropolis–Hastings moves for the number and locations of latent points and for $\lambda$, elliptical slice sampling for the function values, Gibbs updates for $\theta$). A heterochronous version replaces $C_k$ by the lineage-pair counts on the subintervals between sampling and coalescent times.

## Depends on

- [Coalescent point process and thinning simulation](coalescent-point-process-and-thinning-simulation.md)

## Expansion

This adapts the sigmoidal Gaussian Cox process construction for nonparametric estimation of inhomogeneous Poisson intensities to the coalescent, using the fact that the coalescent with variable population size is a point process with a conditional intensity. The upper bound $\lambda$ on $1/N_e$ is not identifiable from the genealogy alone and is given an informative prior, uniform below a guessed bound and exponential above it. Using Brownian motion as the Gaussian process, with covariance $\min(t,t')/\theta$, gives a tridiagonal precision matrix and linear-time updates at the thousands of observed and latent points. Posterior summaries of $N_e(t)$ on any grid are obtained from the predictive distribution of $f$ given its sampled values. In the paper's simulations this approach estimated population trajectories with better accuracy and precision than a Gaussian Markov random field method, and the method does not need a fixed time grid.

## Sources

- Julia A. Palacios, Vladimir N. Minin, Gaussian process-based Bayesian nonparametric inference of population trajectories from gene genealogies, *Biometrics* 69 (2013), 8–18, <https://doi.org/10.1111/biom.12003>; preprint arXiv:1112.4138, <https://doi.org/10.48550/arXiv.1112.4138>.
