/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Corestriction

open CategoryTheory groupCohomology

universe u

/-- Unfolding: corestriction on cocycles agrees pointwise with `cor₂`. -/
example {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex]
    (A : Rep k G) (τ : groupCohomology.Cores.Transversal H)
    (u : cocycles₂ (Rep.res H.subtype A)) :
    (groupCohomology.Cores.corCocycles₂ A τ u : G × G → A) =
      groupCohomology.Cores.cor₂ A τ u :=
  groupCohomology.Cores.coe_corCocycles₂ A τ u

/-- Nontrivial instance: for `H = ⊥` in a finite group over `ℚ`,
with the trivial representation, corestriction sends the class of a
2-cocycle to the class of its corestricted cocycle. All hypotheses
(`FiniteIndex`, transversal, representation) are instantiated. -/
example :
    let H : Subgroup (Multiplicative (ZMod 2)) := ⊥
    let A : Rep ℚ (Multiplicative (ZMod 2)) :=
      Rep.trivial ℚ (Multiplicative (ZMod 2)) ℚ
    ∀ (τ : groupCohomology.Cores.Transversal H)
      (u : cocycles₂ (Rep.res H.subtype A)),
      groupCohomology.Cores.cores A τ (H2π _ u) =
        H2π A (groupCohomology.Cores.corCocycles₂ A τ u) :=
  fun τ u => groupCohomology.Cores.cores_H2π _ τ u

/-- The corestriction API is available in a higher universe. -/
example {k G : Type (u + 1)} [CommRing k] [Group G] {H : Subgroup G}
    [H.FiniteIndex] (A : Rep k G) (τ : groupCohomology.Cores.Transversal H)
    (u : cocycles₂ (Rep.res H.subtype A)) :
    groupCohomology.Cores.cores A τ (H2π _ u) =
      H2π A (groupCohomology.Cores.corCocycles₂ A τ u) :=
  groupCohomology.Cores.cores_H2π A τ u
