# The entropy satisfies McCann's condition

In every dimension $d$, $A(s) = s \log s$ satisfies [McCann's condition (A1)](mc-cann-condition.md):
$A(0) = 0$ with the convention $0 \log 0 = 0$, and its [dilation profile](dilation-profile-entropy.md)
$-d \log \lambda$ is convex and nonincreasing on $(0, \infty)$. With McCann's Theorem 2.2 this is
the displacement convexity of the entropy $\int \rho \log \rho$, the functional whose
Wasserstein gradient flow is the heat equation.

## Background

- [Negative Boltzmann entropy](../wasserstein-gradient-flows-and-the-jko-scheme/neg-entropy.md):
  the same functional in the JKO scheme.

## Sources

- R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179, condition (A1); the computation of the profile is elementary.
