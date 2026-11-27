# Each linkage class has nonnegative deficiency

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finitely many reactions. Every linkage class `θ` of `N` has nonnegative
[deficiency](linkage-class-deficiency.md), `0 ≤ δ_θ`, that is, `s_θ ≤ n_θ - 1`. The proof applies
[the nonnegativity of the deficiency](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/card-sub-card-sub-finrank-nonneg.md)
`n - ℓ - s` (numbers of complexes and of linkage classes, and dimension of the stoichiometric
subspace) to the reactions of `θ` on the complexes of `θ`, whose linkage graph is connected, so
that `ℓ = 1`.

## Sources

- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268.
- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019).
