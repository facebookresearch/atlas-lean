# ∑ δ_θ = δ iff the linkage-class subspaces are independent

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`. The
[deficiencies `δ_θ` of its linkage classes](linkage-class-deficiency.md) sum to its
[deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) `δ`,

`∑_θ δ_θ = δ`,

if and only if the
[stoichiometric subspaces `𝒮_θ` of the linkage classes](linkage-class-stoichiometric-subspace.md)
are independent: each `𝒮_θ` meets the sum of the others only in `0`. Since the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md) is
[their sum](stoichiometric-subspace-eq-i-sup.md), independence says that it is the direct sum
`𝒮 = ⊕_θ 𝒮_θ`. The condition `∑_θ δ_θ = δ` is one of the hypotheses of Feinberg's deficiency-one
theorem.

## Sources

- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268.
- M. Feinberg, *The existence and uniqueness of steady states for a class of chemical reaction
  networks*, Arch. Rational Mech. Anal. 132 (1995) 311–370.
