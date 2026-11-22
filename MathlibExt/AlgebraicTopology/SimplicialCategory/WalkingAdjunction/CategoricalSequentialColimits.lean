/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ProjectiveColimit
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory

/-!
# Categorical weak maps on original sequential colimits

Reuse the named Joyal model and its original same-cardinal generation
datum to instantiate the existing projective functor model. Initial
cofibrancy and the original monic transitions give projective
cofibrancy of both sequences. The genuine colimit–constant Quillen
adjunction then yields the original whole weak colimit map.
No weak preservation from pointwise maps alone is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

private theorem cofibration_of_mono {X Y : JoyalSSet.{u}} (f : X ⟶ Y) [Mono f] :
    Cofibration f := by
  rw [cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations f
  rw [JoyalSSet.modelCategory_cofibrations]
  exact inferInstance

private theorem ofSSet_cofibrant (X : SSet.{u}) : IsCofibrant (JoyalSSet.ofSSet.obj X) :=
  (isCofibrant_iff_of_isInitial (JoyalSSet.ofSSet.map (initial.to X))
    (initialIsInitial.isInitialObj JoyalSSet.ofSSet (⊥_ SSet.{u}))).mpr
      (cofibration_of_mono _)

private theorem mem_weak_iff_categorical {X Y : SSet.{u}} (f : X ⟶ Y) :
    weakEquivalences JoyalSSet.{u} (JoyalSSet.ofSSet.map f) ↔ categoricalEquivalences f := by
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (JoyalSSet.ofSSet.map f) ↔ categoricalEquivalences f
  rw [JoyalSSet.modelCategory_weakEquivalences]
  rfl

/-- An original pointwise categorical equivalence between sequences with monic transitions is categorical on their whole supplied sequential colimit map. -/
theorem categoricalEquivalences_of_sequence_isColimits
    {F G : ℕ ⥤ SSet.{u}} (α : F ⟶ G)
    (hstepF : ∀ n : ℕ, Mono (F.map (homOfLE (n.le_add_right 1))))
    (hstepG : ∀ n : ℕ, Mono (G.map (homOfLE (n.le_add_right 1))))
    (hα : ∀ n, categoricalEquivalences (α.app n))
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ n, cF.ι.app n ≫ d = α.app n ≫ cG.ι.app n) :
    categoricalEquivalences d := by
  obtain ⟨κ, regular, h⟩ := JoyalSSet.exists_joyal_modelCategory.{u}.choose_spec.choose_spec
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨cg, _⟩ := h
  let _ : ModelCategory (ℕ ⥤ JoyalSSet.{u}) := FunctorProjective.modelCategory.{u} (J := ℕ) cg
  let F' := F ⋙ JoyalSSet.ofSSet
  let G' := G ⋙ JoyalSSet.ofSSet
  let α' := Functor.whiskerRight α JoyalSSet.ofSSet
  let _ : IsCofibrant (F'.obj 0) := ofSSet_cofibrant (F.obj 0)
  let _ : IsCofibrant (G'.obj 0) := ofSSet_cofibrant (G.obj 0)
  have hf : ∀ n : ℕ, Cofibration (F'.map (homOfLE (n.le_add_right 1))) := by
    intro n
    let _ : Mono (F.map (homOfLE (n.le_add_right 1))) := hstepF n
    exact cofibration_of_mono (JoyalSSet.ofSSet.map (F.map (homOfLE (n.le_add_right 1))))
  have hg : ∀ n : ℕ, Cofibration (G'.map (homOfLE (n.le_add_right 1))) := by
    intro n
    let _ : Mono (G.map (homOfLE (n.le_add_right 1))) := hstepG n
    exact cofibration_of_mono (JoyalSSet.ofSSet.map (G.map (homOfLE (n.le_add_right 1))))
  have hα' : ∀ n, weakEquivalences JoyalSSet.{u} (α'.app n) :=
    fun n => (mem_weak_iff_categorical (α.app n)).mpr (hα n)
  have hw : WeakEquivalence (JoyalSSet.ofSSet.map d) :=
    ProjectiveColimit.weakEquivalence_of_sequence_isColimits
      (FunctorProjective.fibrations_eq.{u} cg) (FunctorProjective.trivialFibrations_eq.{u} cg)
      (FunctorProjective.weakEquivalences_eq.{u} cg) α' hf hg hα'
      (isColimitOfPreserves JoyalSSet.ofSSet hcF) (isColimitOfPreserves JoyalSSet.ofSSet hcG)
      (JoyalSSet.ofSSet.map d) (fun n => by
        change JoyalSSet.ofSSet.map (cF.ι.app n) ≫ JoyalSSet.ofSSet.map d =
          JoyalSSet.ofSSet.map (α.app n) ≫ JoyalSSet.ofSSet.map (cG.ι.app n)
        simpa only [Functor.map_comp] using congrArg JoyalSSet.ofSSet.map (hd n))
  exact (mem_weak_iff_categorical d).mp ((weakEquivalence_iff _).mp hw)

end SSet.WalkingAdjunction
