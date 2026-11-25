/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Actual Quillen transfer along a weak left comparison

A natural weak comparison with an actual Quillen left adjoint transfers
the trivial-cofibration law whenever the original left adjoint already
preserves cofibrations. The proof uses the literal naturality square and
actual two-out-of-three in the target model. No Quillen outcome for the
original adjunction or weak right-mate hypothesis is assumed.
-/

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [IsQuillenAdjunction adj₂]

include adj₂ in
/-- The original adjunction is genuinely Quillen from actual cofibration preservation and a full
weak natural
comparison to the second actual Quillen adjunction. -/
theorem of_weak_left_comparison (α : L₁ ⟶ L₂)
    (hα : ∀ X : C, WeakEquivalence (α.app X)) (hL : PreservesCofibrations L₁) :
    IsQuillenAdjunction adj₁ := by
  refine ⟨hL, ?_⟩
  intro X Y f hf
  have h₂ := preservesTrivialCofibrations (adj := adj₂) f hf
  let _ : WeakEquivalence (L₂.map f) := (weakEquivalence_iff _).mpr h₂.2
  let _ : WeakEquivalence (α.app X) := hα X
  let _ : WeakEquivalence (α.app Y) := hα Y
  have hcomp : WeakEquivalence (L₁.map f ≫ α.app Y) := by
    rw [α.naturality f]
    infer_instance
  exact ⟨hL f hf.1, (weakEquivalence_iff _).mp
    ((weakEquivalence_postcomp_iff (L₁.map f) (α.app Y)).mp hcomp)⟩

end CategoryTheory.Adjunction.IsQuillenAdjunction
