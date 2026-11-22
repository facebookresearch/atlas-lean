/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ConstantEvaluation
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Constant extension and evaluation for the original localized model

The terminal-site constant/evaluation adjunction is Quillen from scalar
Kan–Quillen simplicial sets to the internally chosen original Smith
localization. Constant scalar trivial cofibrations are objectwise weak and
therefore locally weak. Evaluation consequently preserves the global
fibration and trivial-fibration classes of that same chosen model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.ConstantEvaluation

variable {D : Type w} [Category.{v} D]

private theorem constant_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono ((constant (D := D)).map f) :=
  NatTrans.mono_of_mono_app _

variable [Small.{u} D] [LocallySmall.{u} D] {I : Type i} [Small.{u} I]

/-- Constant extension is left Quillen for the actual original-family Smith model. -/
theorem isQuillenAdjunction (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) :
    @Adjunction.IsQuillenAdjunction
      SSet.{u} inferInstance (SimplicialPresheaf.{u} D) inferInstance
      SSet.modelCategoryQuillen.modelCategory (InjectiveKan.originalLocalSmithData S).model
      constant (evaluation z) (adjunction hz) := by
  let d := InjectiveKan.originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  refine { preservesCofibrations := ?_, preservesTrivialCofibrations := ?_ }
  · intro K L f hf
    change (InjectiveKan.originalLocalSmithData S).model.categoryWithCofibrations.cofibrations
      (constant.map f)
    rw [(InjectiveKan.originalLocalSmithData S).cofibrations_eq]
    have hmono : Mono f := by
      simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using hf
    let _ : Mono f := hmono
    exact constant_mono f
  · intro K L f hf
    change (d.model.categoryWithCofibrations.cofibrations ⊓
      d.model.categoryWithWeakEquivalences.weakEquivalences) (constant.map f)
    rw [d.cofibrations_eq, d.weakEquivalences_eq]
    have hmono : Mono f := by
      simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using hf.1
    let _ : Mono f := hmono
    refine ⟨constant_mono f, ?_⟩
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (InjectiveKan.data D).model
    apply InjectiveKan.weakEquivalences_le_originalLocalEquivalences S
    change (InjectiveKan.data D).model.categoryWithWeakEquivalences.weakEquivalences
      (constant.map f)
    rw [(InjectiveKan.data D).weakEquivalences_eq]
    intro a
    exact hf.2

/-- Evaluation preserves the chosen localization's global fibrations. -/
theorem evaluation_fibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : (InjectiveKan.originalLocalSmithData S).model.categoryWithFibrations.fibrations p) :
    fibrations SSet.{u} (p.app (op z)) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) :=
    (InjectiveKan.originalLocalSmithData S).model
  let _ : (adjunction hz).IsQuillenAdjunction := isQuillenAdjunction S hz
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adjunction hz) p hp

/-- Evaluation preserves the global trivial fibrations of the same chosen model. -/
theorem evaluation_trivialFibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : (InjectiveKan.originalLocalSmithData S).model.categoryWithFibrations.fibrations p ∧
      (InjectiveKan.originalLocalSmithData S).model.categoryWithWeakEquivalences.weakEquivalences
        p) :
    trivialFibrations SSet.{u} (p.app (op z)) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) :=
    (InjectiveKan.originalLocalSmithData S).model
  let _ : (adjunction hz).IsQuillenAdjunction := isQuillenAdjunction S hz
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adjunction hz) p hp

/-- The terminal value of an original local-fibrant presheaf is scalar fibrant. -/
theorem evaluation_isFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (X : SimplicialPresheaf.{u} D)
    (hX : InjectiveKan.isOriginalLocalFibrant S X) : IsFibrant (X.obj (op z)) := by
  let d := InjectiveKan.originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (adjunction hz).IsQuillenAdjunction := isQuillenAdjunction S hz
  have hf : IsFibrant X := (d.isFibrant_iff X).mpr hX
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adjunction hz) hf

end SimplicialPresheaf.ConstantEvaluation
