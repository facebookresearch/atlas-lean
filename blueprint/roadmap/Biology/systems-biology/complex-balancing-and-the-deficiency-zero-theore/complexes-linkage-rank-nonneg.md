# Deficiency via the stoichiometric matrix rank, and its nonnegativity

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and finite reaction set $\rho$, with $n$
[complexes](../../../Dynamics/smooth-dynamics/complexes.md), $\ell$ connected components of its
[linkage graph](../../../Dynamics/smooth-dynamics/linkage-graph.md) and
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md) of dimension
$s$. Let $\Gamma$ be the stoichiometric matrix, the real $S \times \rho$ matrix whose column $r$ is
$\mathrm{prod}(r) - \mathrm{src}(r)$, and $\operatorname{rank} \Gamma$ its rank over $\mathbb{R}$.
Then, computed in the integers,

$$n - \ell - s = n - \ell - \operatorname{rank} \Gamma \ge 0.$$

So the [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) of $N$ can be computed with
$\operatorname{rank} \Gamma$ in place of $s$, and it is nonnegative.

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), § 6.4.
- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268, § 3.
