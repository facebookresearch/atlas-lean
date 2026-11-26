# Generating function of the time-inhomogeneous linear birth–death process

**Setting.** Each individual independently gives birth at rate $\beta(t)$ and dies at rate $\delta(t)$, with $\beta, \delta$ continuously differentiable and nonnegative on $[0,\infty)$. Let $Z(t)$ be the population size at time $t$ started from $Z(0) = 1$ and put

$$D(t) = \int_0^t \big(\delta(u) - \beta(u)\big)\,du, \qquad W(t) = 1 + e^{-D(t)}\int_0^t \beta(u)\,e^{D(u)}\,du .$$

**Theorem.** For $s \in [0,1]$ and $t > 0$,

$$\mathbb{E}\big[s^{Z(t)}\big] = \frac{A(t) + \big(1 - A(t) - B(t)\big)s}{1 - B(t)s}, \qquad A(t) = 1 - \frac{e^{-D(t)}}{W(t)}, \quad B(t) = 1 - \frac{1}{W(t)}.$$

Equivalently, $Z(t)$ is $0$ with probability $A(t)$ and otherwise geometric on $\{1,2,\dots\}$ with success probability $1 - B(t)$; in particular $\mathbb{P}(Z(t) = 0) = A(t)$ and $\mathbb{E}Z(t) = e^{-D(t)}$.

## Depends on

- [Generating-function equation of a time-inhomogeneous Sevast'yanov branching process](generating-function-equation-of-the-inhomogeneous-sevastyanov-process.md)

## Expansion

The birth–death process is the symmetric Sevast'yanov process with exponential lifetimes of rate $\beta(t) + \delta(t)$ and offspring $N \in \{0, 2\}$, chosen with probabilities $\delta/(\beta+\delta)$ and $\beta/(\beta+\delta)$ (a birth is modeled as the branch ending and two new branches starting). Differentiating the integral equation in the birth time gives the backward Kolmogorov equation $\partial_\tau F = (\beta + \delta)F - \delta - \beta F^2$, a Riccati equation; the linear-fractional ansatz reduces it to linear ODEs for $A$ and $B$, whose solution is Kendall's 1948 formula.

## Sources

- F. M. Andersen, M. A. Suchard, C. Wiuf and S. Bhatt, "Inhomogeneous branching trees with symmetric and asymmetric offspring and their genealogies", arXiv:2510.07921 (2025), Proposition 3.11, <https://doi.org/10.48550/arXiv.2510.07921>.
- D. G. Kendall, "On the generalized 'birth-and-death' process", Annals of Mathematical Statistics 19 (1948), <https://doi.org/10.1214/aoms/1177730285>.
