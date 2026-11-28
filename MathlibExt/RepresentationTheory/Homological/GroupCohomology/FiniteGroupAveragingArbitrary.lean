/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionArbitrary

/-!
# Finite-group cohomology vanishes in all positive degrees after averaging

Let R be a commutative ring, G a finite group, and A an R-linear representation in universe u.
If |G| is a unit in R, then H^{n+1}(G,A) is zero for every n≥0. The results state this as
subsingleton coefficients, vanishing of each class, and the zero-object property in R-modules.

Restriction to the trivial subgroup is injective because restriction followed by corestriction
on the ambient cohomology is multiplication by the subgroup index |G|. The positive cohomology
of the trivial subgroup is zero, so the ambient positive cohomology vanishes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Let R be a commutative ring, G a finite group, and A an R-linear G-representation, in the given
universe u. Assume m=|G| is a unit in R and write m⁻¹ for the coefficient of its inverse unit.
For every n≥0, H^{n+1}(G,A) is subsingleton. Restriction to the trivial subgroup is injective
under this unit hypothesis, and its target positive cohomology is zero. -/
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

/-- Let R be a commutative ring, G a finite group, and A an R-linear G-representation, in the given
universe u. Assume m=|G| is a unit in R and write m⁻¹ for the coefficient of its inverse unit.
For n≥0 and x∈H^{n+1}(G,A), one has x=0. The statement holds for every R-linear coefficient
representation A and every positive cohomological degree. -/
theorem eq_zero_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) (n : ℕ)
    (x : groupCohomology A (n + 1)) : x = 0 := by
  let _ : Subsingleton (groupCohomology A (n + 1)) :=
    succ_subsingleton_of_card_isUnit A hcard n
  exact Subsingleton.elim _ _

/-- Let R be a commutative ring, G a finite group, and A an R-linear G-representation, in the given
universe u. Assume m=|G| is a unit in R and write m⁻¹ for the coefficient of its inverse unit.
For every n≥0, H^{n+1}(G,A) is a zero object of the category of R-modules. Equivalently its
underlying module has only the zero element, and every module map into or out of it is the zero
morphism. -/
theorem isZero_succ_of_card_isUnit
    (A : Rep R G) (hcard : IsUnit (Fintype.card G : R)) (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology A (n + 1)) := by
  let _ : Subsingleton (groupCohomology A (n + 1)) :=
    succ_subsingleton_of_card_isUnit A hcard n
  exact ModuleCat.isZero_of_subsingleton _

end groupCohomology
