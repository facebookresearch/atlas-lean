# Finite-support Tweedie score identity

Let $\theta$ be valid parameters of a $K$-component isotropic Gaussian mixture in $\mathbb{R}^d$
with weights $\pi_k$, a common variance $v > 0$, and means $\mu_k = \lambda x_k$ for points
$x_1, \dots, x_K \in \mathbb{R}^d$ and a real $\lambda$. Let
$p(z) = \sum_k \pi_k \mathcal{N}(z \mid \lambda x_k, v I)$ be the mixture density and
$r_k(z)$ the responsibilities (posterior component weights) at $z$. Then for every
$z \in \mathbb{R}^d$,

$$\nabla \log p(z) = \frac{\lambda\, m(z) - z}{v}, \qquad m(z) = \sum_k r_k(z)\, x_k .$$

If $X$ takes the value $x_k$ with probability $\pi_k$, $G$ is a standard Gaussian vector
independent of $X$ and $Z = \lambda X + \sqrt v\, G$, then $p$ is the density of $Z$ and $m(z)$ is a
version of $\mathbb{E}[X \mid Z = z]$, so this is the finite-support case of Tweedie's identity
$\nabla \log p(z) = (\lambda\, \mathbb{E}[X \mid Z = z] - z)/v$, which S. Mei and Y. Wu, *Deep
networks as denoising algorithms: sample-efficient learning of diffusion models in
high-dimensional graphical models*, arXiv:2309.11420 (version 1), page 5, state without proof for
general laws of $X$.

## Background

- [Tweedie's formula](../../../../Probability/bayesian-statistics/empirical-bayes-and-tweedie-s-formula/gaussian-posterior-mean-eq-add-mul-deriv.md): the one-dimensional formula for an arbitrary prior on the mean, with the posterior mean identified with a conditional expectation when the prior has a finite first moment; it covers the general one-dimensional case that this page leaves open.
