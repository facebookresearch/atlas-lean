/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The fibrant-object criterion for Quillen adjunctions

A cofibration is trivial exactly when it lifts against every fibration between
fibrant objects. Consequently, an adjunction is Quillen exactly when its left
adjoint preserves cofibrations and its right adjoint preserves fibrations between
fibrant objects. No cofibrancy hypothesis is required on either endpoint of a
fibration in the test class, and the right adjoint need not preserve the fibrancy
of those endpoints as part of the hypothesis.

## References

* André Joyal and Myles Tierney, *Quasi-categories vs Segal spaces*, §7,
  Lemma 7.14 and Proposition 7.15 (https://arxiv.org/abs/math/0607820v2).

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]

/-- Fibrations whose source and target are fibrant. -/
def fibrationsBetweenFibrantObjects : MorphismProperty C :=
  fun X Y p ↦ fibrations C p ∧ IsFibrant X ∧ IsFibrant Y

/-- A functor takes every fibration between fibrant objects to a fibration.
No condition is imposed on the fibrancy of the image objects. -/
def PreservesFibrationsBetweenFibrantObjects
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D] (F : C ⥤ D) : Prop :=
  fibrationsBetweenFibrantObjects ≤ (fibrations D).inverseImage F

/-- Joyal–Tierney Lemma 7.14: among cofibrations, lifting against all fibrations
between fibrant objects detects the trivial cofibrations. -/
theorem trivialCofibration_iff_llp_fibrationsBetweenFibrantObjects
    {A B : C} (i : A ⟶ B) (hi : cofibrations C i) :
    trivialCofibrations C i ↔ (fibrationsBetweenFibrantObjects (C := C)).llp i := by
  constructor
  · intro hiT X Y p hp
    exact hasLiftingProperty_of_wfs i p hiT hp.1
  · intro hiLift
    let j := FibrantObject.HoCat.iResolutionObj B
    let d := factorizationData (trivialCofibrations C) (fibrations C) (i ≫ j)
    have : Fibration d.p := (fibration_iff _).mpr d.hp
    have : IsFibrant d.Z := isFibrant_of_fibration d.p
    have : HasLiftingProperty i d.p := hiLift d.p ⟨d.hp, inferInstance, inferInstance⟩
    let sq : CommSq d.i i d.p j := ⟨d.fac⟩
    let Q := (weakEquivalences C).Q
    have : IsIso (Q.map d.i) := Localization.inverts Q _ d.i d.hi.2
    have : IsIso (Q.map j) := Localization.inverts Q _ j (mem_weakEquivalences _)
    have hMapLift : Q.map sq.lift ≫ Q.map d.p = Q.map j := by
      rw [← Q.map_comp, sq.fac_right]
    have hMapFactor : Q.map i ≫ Q.map sq.lift = Q.map d.i := by
      rw [← Q.map_comp, sq.fac_left]
    have : Mono (Q.map sq.lift) := mono_of_mono_fac hMapLift
    have : IsSplitEpi (Q.map sq.lift) := IsSplitEpi.mk'
      { section_ := inv (Q.map d.i) ≫ Q.map i
        id := by rw [Category.assoc, hMapFactor, IsIso.inv_hom_id] }
    have : IsIso (Q.map sq.lift) := isIso_of_mono_of_isSplitEpi _
    have : IsIso (Q.map i) := IsIso.of_isIso_fac_right hMapFactor
    exact ⟨hi, (weakEquivalence_iff_isIso_map_of_isLocalization Q i).mpr inferInstance⟩

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

open HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

/-- A left adjoint preserving all cofibrations and a right adjoint preserving
fibrations between fibrant objects define a Quillen adjunction. -/
theorem mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
    (hL : PreservesCofibrations L) (hR : PreservesFibrationsBetweenFibrantObjects R) :
    IsQuillenAdjunction adj where
  preservesCofibrations := hL
  preservesTrivialCofibrations := by
    intro A B i hi
    apply (trivialCofibration_iff_llp_fibrationsBetweenFibrantObjects
      (L.map i) (hL i hi.1)).mpr
    intro X Y p hp
    exact (adj.hasLiftingProperty_iff i p).mpr
      (hasLiftingProperty_of_wfs i (R.map p) hi (hR p hp))

/-- Joyal–Tierney Proposition 7.15: a Quillen adjunction is equivalently one
whose left adjoint preserves cofibrations and whose right adjoint preserves
fibrations between fibrant objects. -/
theorem iff_preservesCofibrations_and_fibrationsBetweenFibrantObjects :
    IsQuillenAdjunction adj ↔
      PreservesCofibrations L ∧ PreservesFibrationsBetweenFibrantObjects R := by
  constructor
  · intro h
    refine ⟨h.preservesCofibrations, ?_⟩
    intro X Y p hp
    exact preservesFibrations (adj := adj) p hp.1
  · rintro ⟨hL, hR⟩
    exact mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects hL hR

end CategoryTheory.Adjunction.IsQuillenAdjunction
