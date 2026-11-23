# McCann's condition for displacement convexity

An internal-energy density $A$ satisfies McCann's condition (A1) in dimension $d$ if $A(0) = 0$ and
its dilation profile $\lambda \mapsto \lambda^d A(\lambda^{-d})$ is convex and nonincreasing on
$(0, \infty)$; here $A$ is real-valued. Under this condition McCann's theorem makes the internal
energy $U(\rho) = \int A(\rho(x))\, dx$ convex along displacement interpolation between absolutely
continuous probability measures on $\mathbb{R}^d$.

## Idea

McCann interpolates between two probability densities along optimal transport, the geodesics of
the Wasserstein distance $W_2$, rather than linearly. The dilation profile is the energy of a unit
mass spread uniformly over a region and dilated by the factor $\lambda$. Since dilations are
displacement interpolants, convexity of the profile is necessary for displacement convexity, and
McCann's theorem is that it is also sufficient. The examples here are the entropy $s \log s$, which
satisfies the condition in every dimension and plays the role of the case $m = 1$, and, for an
integer $d \ge 1$ and $m > 0$ with $m \ne 1$, the porous-medium energies $s^m / (m - 1)$, which
satisfy it exactly when $m \ge 1 - 1/d$. These are the energies whose Wasserstein gradient flows
are the heat, porous medium and fast diffusion equations.

## Statements

- [McCann's condition (A1)](mc-cann-condition.md)
- [Dilation profile of an internal energy](dilation-profile.md): the function in the condition.
- [The entropy satisfies McCann's condition](mc-cann-condition-entropy.md): an example, the entropy.
- [Dilation profile of the entropy](dilation-profile-entropy.md): used for the entropy example.
- [McCann's threshold $m \ge 1 - 1/d$ for porous-medium energies](mc-cann-condition-porous-medium-iff.md): an example, porous-medium energies with $0 < m < 1$.
- [Porous-medium energies with $m > 1$ satisfy McCann's condition](mc-cann-condition-porous-medium-of-one-l.md): an example, porous-medium energies with $m > 1$.
- [Dilation profile of a porous-medium energy](dilation-profile-porous-medium.md): used for the porous-medium examples.
- [Convexity of negative powers](convex-on-rpow-neg.md): a lemma for the case $m > 1$.

## Sources

- R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997).

## Related topics

- [Wasserstein gradient flows and the JKO scheme](../wasserstein-gradient-flows-and-the-jko-scheme/README.md):
  the entropy and the porous-medium energies are the functionals whose Wasserstein gradient flows
  are the heat and porous medium equations.
- [Brenier's theorem](../brenier-s-theorem/brenier.md): the optimal map $\nabla \psi$ along which McCann
  interpolates.
- [Transport-cost inequalities](../../../Probability/concentration-inequalities/transport-cost-inequalities/README.md):
  convexity of the relative entropy along displacement interpolation underlies the HWI and
  Talagrand inequalities.
