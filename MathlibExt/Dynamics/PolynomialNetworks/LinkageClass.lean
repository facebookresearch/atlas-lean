/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linkage classes of a reaction network

The linkage classes of a network `N : ReactionNetwork S ρ` are the connected components of its
undirected reaction graph `N.linkageGraph` on the complexes. Each linkage class `θ` carries its
own reactions, stoichiometric subspace `𝒮_θ`, deficiency `δ_θ = n_θ - 1 - s_θ` (`n_θ` complexes
in the class and `s_θ = dim 𝒮_θ`), and part of the mass-action field. These are the objects of
Feinberg's deficiency-one theorem.

## Main definitions

* `linkageClassOf r`: the linkage class of the reaction `r` (that of its source complex);
* `linkageClassNetwork θ`: the reactions of the linkage class `θ`, as a network on `S`;
* `linkageClassStoichiometricSubspace θ`: the span `𝒮_θ` of their reaction vectors;
* `linkageClassDeficiency θ`: for finitely many complexes (`[Finite N.complexes]`),
  `δ_θ = n_θ - 1 - s_θ`;
* `linkageClassField θ k x`: for finite species (`[Fintype S]`) and finite reactions
  (`[Fintype ρ]`), the part
  `∑_{r : ρ, linkageClassOf r = θ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)` of the
  mass-action field contributed by the reactions of `θ`.

Their linear algebra (`𝒮 = ∑_θ 𝒮_θ`, and for networks with finitely many species, reactions, and
linkage classes, `∑_θ δ_θ ≤ δ` with equality iff the `𝒮_θ` are independent, together with the
decoupling of the equilibrium equations) is developed in `Domains.Biology.Dynamics.DeficiencyOne`.

## References

* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42 (1987)
  2229–2268.
* M. Feinberg, "The existence and uniqueness of steady states for a class of chemical reaction
  networks", Arch. Rational Mech. Anal. 132 (1995) 311–370.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019).
-/

@[expose] public section

open Finset Module

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The linkage class of the reaction `r`: the connected component of its source complex in
the linkage graph (its product complex lies in the same class). -/
def linkageClassOf (r : ρ) : N.linkageGraph.ConnectedComponent :=
  N.linkageGraph.connectedComponentMk ⟨N.src r, Or.inl ⟨r, rfl⟩⟩

/-- The reactions of the linkage class `θ`, as a reaction network on the same species. -/
def linkageClassNetwork (θ : N.linkageGraph.ConnectedComponent) :
    ReactionNetwork S {r // N.linkageClassOf r = θ} where
  src r := N.src r
  prod r := N.prod r

/-- The stoichiometric subspace `𝒮_θ` of the linkage class `θ`: the span of the reaction
vectors `prod r - src r` of its reactions.

Source: Feinberg (1987); Feinberg (2019). -/
def linkageClassStoichiometricSubspace (θ : N.linkageGraph.ConnectedComponent) :
    Submodule ℝ (S → ℝ) :=
  (N.linkageClassNetwork θ).stoichiometricSubspace

/-- For a network with finitely many complexes (`[Finite N.complexes]`), the deficiency
`δ_θ = n_θ - 1 - s_θ` of the linkage class `θ`, where `n_θ` is the number of complexes in `θ` and
`s_θ = dim 𝒮_θ`.

Source: Feinberg (1987); Feinberg (1995). -/
noncomputable def linkageClassDeficiency [Finite N.complexes]
    (θ : N.linkageGraph.ConnectedComponent) : ℤ :=
  (Nat.card θ.supp : ℤ) - 1 - finrank ℝ (N.linkageClassStoichiometricSubspace θ)

open Classical in
/-- For a network with finite species set `S` (`[Fintype S]`) and finite reaction set `ρ`
(`[Fintype ρ]`), the part of the mass-action field with rate constants `k` contributed by the
reactions of the linkage class `θ`:
`x ↦ ∑_{r : ρ, linkageClassOf r = θ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)`. It is
defined for all real `k` and `x`; the powers are natural powers, so `x_s ^ 0 = 1` also at
`x_s = 0`. -/
noncomputable def linkageClassField [Fintype S] [Fintype ρ]
    (θ : N.linkageGraph.ConnectedComponent) (k : ρ → ℝ) (x : S → ℝ) : S → ℝ :=
  fun s => ∑ r ∈ univ.filter (fun r => N.linkageClassOf r = θ),
    k r * (∏ s', x s' ^ N.src r s') * ((N.prod r s : ℝ) - N.src r s)

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
