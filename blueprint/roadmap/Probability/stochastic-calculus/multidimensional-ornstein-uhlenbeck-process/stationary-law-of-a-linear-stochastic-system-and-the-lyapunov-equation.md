# Stationary law of a linear stochastic system and the Lyapunov equation

This node covers the stationary covariance of a multidimensional Ornstein-Uhlenbeck process. Let $A$ be a real $n \times n$ matrix whose
eigenvalues have negative real parts, $B$ a real $n \times k$ matrix and $W$ a $k$-dimensional Brownian motion, and let $X$ solve
$dX_t = AX_t\,dt + B\,dW_t$ with $X_0$ independent of $W$. Then the Lyapunov equation

$$A\Sigma + \Sigma A^{\mathsf T} + BB^{\mathsf T} = 0$$

has exactly one solution, $\Sigma = \int_0^\infty e^{As}BB^{\mathsf T}e^{A^{\mathsf T}s}\,ds$, which is symmetric positive semidefinite; the Gaussian
law $N(0, \Sigma)$ is the unique stationary law of $X$; and for every initial law with finite second moment the law of $X_t$ converges weakly
to $N(0, \Sigma)$ as $t \to \infty$.

## Depends on

- [Existence of a stationary Ornstein-Uhlenbeck process](../ornstein-uhlenbeck-process/exists-is-stationary-ornstein-uhlenbeck.md)
- [Asymptotic stability of linear differential equations](../../../Analysis/ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md)

## Expansion

A good expansion writes the solution by the variation-of-constants formula with a vector Itô integral of a deterministic
integrand, computes its mean and covariance by the Itô isometry, and solves the Lyapunov equation by the convergent integral. The mechanical
covariance of a damped oscillator and spectral densities are separate consumers of this node.

## Sources

- L. Arnold, *Stochastic Differential Equations: Theory and Applications*, Wiley, 1974, for linear stochastic differential equations.
