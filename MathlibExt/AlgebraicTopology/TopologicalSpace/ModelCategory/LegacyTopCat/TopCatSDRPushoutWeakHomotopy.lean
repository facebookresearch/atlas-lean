/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCat

/-!
# Pushout legs of strong deformation retracts are weak homotopy equivalences

In a `TopCat` pushout square with attaching map `i : A ⟶ X`, if `i` comes
with a retraction `r`, `retract : i ≫ r = 𝟙 A`, a homotopy
`H : Homotopy (𝟙 X) (r ≫ i)` and the pointwise fix law `stat`, then the
pushed-out leg is a weak homotopy equivalence. This matches the exact
retract/homotopy/fix data of the realized horn inclusions
(`SSet.realizedHornRetract_ι`, `SSet.realizedHornHomotopy`,
`SSet.realizedHornHomotopyMap_fix`).

The pushout retraction is strict via `pushout.desc`; the return homotopy
descends from `H` and the constant leg homotopy via
`TopCat.Homotopy.pushoutDesc`, using only the fix law and pushout
commutativity. Both homotopies cross `TopCat.Homotopy.toSSet` and close by
`SSet.KanComplex.W.of_homotopy`, as in the realized-horn case.

No model structure is introduced and no arbitrary pushout stability is
claimed: only strong-deformation-retract legs are treated, and no
closed/cofibration hypothesis is needed for this direction. An arbitrary
pushout square is covered by transport along `IsPushout.isoIsPushout`
with `cancel_right_of_respectsIso`. The tensor-cylinder route through
`isPushout_prodMap_right_of_isPushout` and `Homotopy.ofCylinder` is left to
callers that already hold a descended cylinder map.
-/

/-- Pushout legs of strong deformation retracts are weak homotopy
equivalences. -/
theorem sdr_pushout_inr_mem_weakHomotopyEquivalences
    {A X Y P : TopCat.{u}} {i : A ⟶ X} {f : A ⟶ Y} {g : X ⟶ P}
    {j : Y ⟶ P} (h : IsPushout i f g j) (r : X ⟶ A)
    (retract : i ≫ r = 𝟙 A) (H : TopCat.Homotopy (𝟙 X) (r ≫ i))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    weakHomotopyEquivalences j := by
  have hP : IsPushout i f (pushout.inl i f) (pushout.inr i f) :=
    IsPushout.of_hasPushout i f
  have hChosen : weakHomotopyEquivalences (pushout.inr i f) := by
    have w : i ≫ r ≫ f = f := by
      rw [← Category.assoc, retract, Category.id_comp]
    set s := pushout.desc (r ≫ f) (𝟙 Y) (w.trans (Category.comp_id _).symm) with hs
    have hs0 : pushout.inl i f ≫ s = r ≫ f := by simp [hs]
    have hs1 : pushout.inr i f ≫ s = 𝟙 Y := by simp [hs]
    have h₀ : i ≫ (𝟙 X ≫ pushout.inl i f) = f ≫ pushout.inr i f := by
      rw [Category.id_comp]
      exact hP.w
    have h₁ : i ≫ ((r ≫ i) ≫ pushout.inl i f) = f ≫ pushout.inr i f := by
      rw [Category.assoc r i (pushout.inl i f),
        ← Category.assoc i r (i ≫ pushout.inl i f), retract,
        Category.id_comp]
      exact hP.w
    have hCompat : ∀ (t : unitInterval) (a : A),
        ((TopCat.Homotopy.refl (pushout.inl i f)).comp H) (t, i a) =
          (TopCat.Homotopy.refl (pushout.inr i f)) (t, f a) := by
      intro t a
      change (pushout.inl i f) (H (t, i a)) = (pushout.inr i f) (f a)
      rw [stat t a]
      exact ConcreteCategory.congr_hom hP.w a
    have K := TopCat.Homotopy.pushoutDesc
      ((TopCat.Homotopy.refl (pushout.inl i f)).comp H)
      (TopCat.Homotopy.refl (pushout.inr i f)) h₀ h₁ hCompat
    have hid : pushout.desc (𝟙 X ≫ pushout.inl i f) (pushout.inr i f) h₀ =
        𝟙 _ := by
      apply pushout.hom_ext
      · rw [pushout.inl_desc, Category.id_comp, Category.comp_id]
      · rw [pushout.inr_desc, Category.comp_id]
    have hsid :
        pushout.desc ((r ≫ i) ≫ pushout.inl i f) (pushout.inr i f) h₁ =
          s ≫ pushout.inr i f := by
      apply pushout.hom_ext
      · rw [pushout.inl_desc, ← Category.assoc, hs0,
          Category.assoc r i _, Category.assoc r f _, ← hP.w]
      · rw [pushout.inr_desc, ← Category.assoc, hs1, Category.id_comp]
    have hPk : TopCat.Homotopy (𝟙 (pushout i f)) (s ≫ pushout.inr i f) :=
      ContinuousMap.Homotopy.cast K
        (congrArg TopCat.Hom.hom hid)
        (congrArg TopCat.Hom.hom hsid)
    have hY : TopCat.Homotopy (pushout.inr i f ≫ s) (𝟙 Y) :=
      ContinuousMap.Homotopy.cast (TopCat.Homotopy.refl (𝟙 Y))
        (congrArg TopCat.Hom.hom hs1.symm) rfl
    have hSP : SSet.Homotopy
        (TopCat.toSSet.map s ≫ TopCat.toSSet.map (pushout.inr i f)) (𝟙 _) := by
      simpa using TopCat.Homotopy.toSSet (TopCat.Homotopy.symm hPk)
    have hPS : SSet.Homotopy
        (TopCat.toSSet.map (pushout.inr i f) ≫ TopCat.toSSet.map s) (𝟙 _) := by
      simpa using hY.toSSet
    have hW : SSet.KanComplex.W (TopCat.toSSet.map (pushout.inr i f)) :=
      @SSet.KanComplex.W.of_homotopy _ _
        (TopCat.toSSet_obj_kanComplex _)
        (TopCat.toSSet_obj_kanComplex _) _ _ hPS hSP
    rw [TopCat.mem_weakHomotopyEquivalences_iff]
    exact hW
  let e := h.isoIsPushout _ _ hP
  have he : j ≫ e.hom = pushout.inr i f := h.inr_isoIsPushout_hom _ _ hP
  have := e.isIso_hom
  have hW' : weakHomotopyEquivalences (j ≫ e.hom) := by
    simpa [he] using hChosen
  exact (weakHomotopyEquivalences.cancel_right_of_respectsIso j e.hom).mp hW'

end TopCat
