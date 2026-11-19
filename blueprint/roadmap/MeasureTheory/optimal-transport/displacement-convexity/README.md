# Displacement convexity

McCann (1997) interpolates between probability densities on $\mathbb{R}^d$ along optimal transport
(the geodesics of $W_2$) rather than linearly. An internal energy $U(\rho) = \int A(\rho) \, dx$ is
convex along this *displacement interpolation* when $A$ satisfies his condition (A1):
$\lambda \mapsto \lambda^d A(\lambda^{-d})$ is convex and nonincreasing on $(0, \infty)$, with $A(0) = 0$
(his Theorem 2.2). The function $\lambda^d A(\lambda^{-d})$ is the energy of a uniform gas dilated by
the factor $\lambda$. The entropy $s \log s$ satisfies (A1) in every dimension, and the porous-medium
energies $s^m/(m-1)$ satisfy it exactly when $m \ge 1 - 1/d$. Otto and Westdickenberg derive the
contraction of the porous medium semigroup in the Wasserstein distance from this convexity
(*Eulerian calculus for the contraction in the Wasserstein distance*, Section 1).

- [Dilation profile of an internal energy](dilation-profile.md)
- [McCann's condition (A1)](mc-cann-condition.md)
- [Dilation profile of the entropy](dilation-profile-entropy.md)
- [The entropy satisfies McCann's condition](mc-cann-condition-entropy.md)
- [Dilation profile of a porous-medium energy](dilation-profile-porous-medium.md)
- [Convexity of negative powers](convex-on-rpow-neg.md)
- [Porous-medium energies with $m > 1$ satisfy McCann's condition](mc-cann-condition-porous-medium-of-one-l.md)
- [McCann's threshold $m \ge 1 - 1/d$ for porous-medium energies](mc-cann-condition-porous-medium-iff.md)

## Related topics

- [Wasserstein gradient flows and the JKO scheme](../wasserstein-gradient-flows-and-the-jko-scheme/README.md):
  the entropy and the porous-medium energies are the functionals whose Wasserstein gradient flows
  are the heat and porous medium equations.
- [Brenier's theorem](../brenier.md): the optimal map $\nabla \psi$ along which McCann
  interpolates.
- [Transport-cost inequalities](../../../Probability/concentration-inequalities/transport-cost-inequalities/README.md):
  convexity of the relative entropy along displacement interpolation underlies the HWI and
  Talagrand inequalities.
