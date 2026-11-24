# Weakly reversible, linear-form deficiency zero: complex balancing

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and finite reaction set $\rho$. Suppose that $N$ is
[weakly reversible](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md): for every reaction
$r$ there is a directed path of reactions, possibly of length zero, from $\mathrm{prod}(r)$ back to
$\mathrm{src}(r)$. Suppose also that $N$ has deficiency zero in the
[linear form](deficiency-eq-zero-iff.md): whenever $\alpha \in \mathbb{R}^\rho$ satisfies
$\sum_{r} \alpha_r (\mathrm{prod}(r) - \mathrm{src}(r)) = 0$ in $\mathbb{R}^S$, every function
$\eta \colon \mathbb{N}^S \to \mathbb{R}$ satisfies

$$\sum_{r \in \rho} \alpha_r \bigl(\eta(\mathrm{prod}(r)) - \eta(\mathrm{src}(r))\bigr) = 0.$$

Then for every choice of rate constants $k_r > 0$ there is $c \in \mathbb{R}_{>0}^S$ that is
[complex balanced](is-complex-balanced.md) for $k$. By
[Complex-balanced states are equilibria](mass-action-field-eq-zero-of-is-complex.md), such a $c$ is
an equilibrium of the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md).

By [Deficiency zero in linear form](deficiency-eq-zero-iff.md), the linear condition is equivalent
to [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) $\delta = 0$; the form of the
theorem with $\delta = 0$ is
[Horn–Feinberg: complex balancing for every choice of rate constants](exists-pos-is-complex-balanced.md).

## Sources

- F. Horn, *Necessary and sufficient conditions for complex balancing in chemical kinetics*,
  Arch. Rational Mech. Anal. 49 (1972) 172–186.
- M. Feinberg, *Complex balancing in general kinetic systems*, Arch. Rational Mech. Anal. 49
  (1972) 187–194.
- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268.
- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), Chapter 16.
