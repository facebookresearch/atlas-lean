/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionArbitrary

/-!
# Finite-group cohomology vanishing in arbitrary positive degree

If the order of a finite group is a unit in the coefficient ring, then its
cohomology with arbitrary linear coefficients vanishes in every positive
degree.  Restriction to the trivial subgroup is injective by the
restriction--corestriction index formula, while the positive cohomology of
the trivial group is zero.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Positive-degree cohomology of a finite group is subsingleton when the
group order is a unit in the coefficient ring. -/
theorem succ_subsingleton_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) (n : ℕ) :
    Subsingleton (groupCohomology A (n + 1)) := by
  let H : Subgroup G := ⊥
  have hindex : IsUnit (H.index : R) := by
    simpa only [H, Subgroup.index_bot, Nat.card_eq_fintype_card] using hcard
  have hinjective : Function.Injective
      (groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype A)) (n + 1)) :=
    restriction_injective_of_isUnit_index (H := H) A (n + 1) hindex
  have hzero : CategoryTheory.Limits.IsZero
      (groupCohomology (Rep.res H.subtype A) (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton
      (Rep.res H.subtype A) n
  let _ : Subsingleton
      (groupCohomology (Rep.res H.subtype A) (n + 1)) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact ⟨fun x y ↦ hinjective (Subsingleton.elim _ _)⟩

/-- Every positive-degree class vanishes when the finite group order is a
unit in the coefficient ring. -/
theorem eq_zero_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) (n : ℕ)
    (x : groupCohomology A (n + 1)) : x = 0 := by
  let _ : Subsingleton (groupCohomology A (n + 1)) :=
    succ_subsingleton_of_card_isUnit A hcard n
  exact Subsingleton.elim _ _

/-- The positive-degree cohomology object is zero when the finite group
order is a unit in the coefficient ring. -/
theorem isZero_succ_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology A (n + 1)) := by
  let _ : Subsingleton (groupCohomology A (n + 1)) :=
    succ_subsingleton_of_card_isUnit A hcard n
  exact ModuleCat.isZero_of_subsingleton _

end groupCohomology
