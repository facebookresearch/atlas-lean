/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
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
# Pushouts of strong deformation retract inclusions

Let `i:A→X`, `f:A→Y`, `g:X→P`, and `j:Y→P` form a pushout in `TopCat.{u}`. Suppose `r:X→A`
satisfies `i≫r=𝟙 A`, and there is a homotopy `H:𝟙 X~r≫i` stationary on `i(A)`:
`H(t,i(a))=i(a)` for every interval parameter and every `a`. Then the pushed-out leg `j` is a
weak homotopy equivalence. The pushout retraction and stationary homotopy give the
corresponding deformation-retract data on that leg.
-/

/-- In `TopCat.{u}`, let `IsPushout i f g j` have legs `i:A→X`, `f:A→Y`, `g:X→P`, and `j:Y→P`.
Suppose `r:X→A` satisfies `i≫r=𝟙 A` and `H : TopCat.Homotopy (𝟙 X) (r≫i)` satisfies `∀ t :
unitInterval, ∀ a : A, H(t,i(a))=i(a)`. Then `TopCat.weakHomotopyEquivalences j`. -/
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
