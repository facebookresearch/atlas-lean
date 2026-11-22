/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Original Hom restriction into a Kan complex

A genuine Kan–Quillen trivial cofibration admits extension of every
supplied original map into a Kan complex. This is the actual model
lifting property, and supplies surjectivity of coefficient Yoneda.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.KanHomRestriction

/-- Every original Hom map into a supplied Kan complex extends along a genuine original trivial cofibration. -/
theorem precompose_surjective (H : SSet.{u}) [KanComplex H]
    {A B : SSet.{u}} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i] :
    Function.Surjective ((yoneda.obj H).map i.op) := by
  intro a
  let sq : CommSq a i (terminal.from H) (terminal.from B) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Coefficient Yoneda into an actual Kan complex maps every genuine opposite-model trivial fibration to a
  surjective map of original Hom sets. -/
theorem coefficient_surjective (H : SSet.{u}) [KanComplex H]
    {A B : SSet.{u}ᵒᵖ} (p : A ⟶ B) (hp : trivialFibrations (SSet.{u}ᵒᵖ) p) :
    Function.Surjective ((yoneda.obj H).map p) := by
  change trivialCofibrations SSet.{u} p.unop at hp
  let _ : Cofibration p.unop := ((mem_trivialCofibrations_iff (f := p.unop)).mp hp).1
  let _ : WeakEquivalence p.unop := ((mem_trivialCofibrations_iff (f := p.unop)).mp hp).2
  exact precompose_surjective H p.unop

end SSet.KanHomRestriction
