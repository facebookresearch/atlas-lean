# Deficiency-zero theorem, weakly reversible case, linear form

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and finite reaction set $\rho$. Suppose that $N$ is
[weakly reversible](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md): for every reaction
$r$ there is a directed path of reactions, possibly of length zero, from $\mathrm{prod}(r)$ back to
$\mathrm{src}(r)$. Suppose also that $N$ has deficiency zero in the
[linear form](deficiency-eq-zero-iff.md): whenever $\alpha \in \mathbb{R}^\rho$ satisfies
$\sum_{r} \alpha_r (\mathrm{prod}(r) - \mathrm{src}(r)) = 0$ in $\mathbb{R}^S$, every function
$\eta \colon \mathbb{N}^S \to \mathbb{R}$ satisfies

$$\sum_{r \in \rho} \alpha_r \bigl(\eta(\mathrm{prod}(r)) - \eta(\mathrm{src}(r))\bigr) = 0.$$

Then for every choice of rate constants $k_r > 0$ and every $x_0 \in \mathbb{R}_{>0}^S$ there is
exactly one $x \in \mathbb{R}_{>0}^S$ with $x - x_0$ in the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md)
$\mathcal{S}$ and $f(x) = 0$, where $f$ is the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md): each positive
stoichiometric compatibility class $(x_0 + \mathcal{S}) \cap \mathbb{R}_{>0}^S$ contains exactly one
equilibrium.

The proof combines
[Weakly reversible, linear-form deficiency zero: complex balancing](exists-pos-is-complex-balanced-of-defici.md)
with
[Horn–Jackson: one equilibrium per compatibility class](exists-unique-equilibrium-of-is-complex.md).
By [Deficiency zero in linear form](deficiency-eq-zero-iff.md), the linear condition is equivalent
to [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) $\delta = 0$; the form of the
theorem with $\delta = 0$ is the
[deficiency-zero theorem, weakly reversible case](exists-unique-equilibrium.md).

## Sources

- F. Horn, *Necessary and sufficient conditions for complex balancing in chemical kinetics*,
  Arch. Rational Mech. Anal. 49 (1972) 172–186.
- F. Horn and R. Jackson, *General mass action kinetics*, Arch. Rational Mech. Anal. 47 (1972)
  81–116.
- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268.
