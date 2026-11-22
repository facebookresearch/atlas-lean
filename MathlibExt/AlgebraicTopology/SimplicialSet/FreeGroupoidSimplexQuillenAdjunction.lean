/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexWeakRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The wrapped k Quillen adjunction

The original raw k adjunction is transported to the designated Joyal carrier.
Monomorphism preservation and the original k weak-class classifier prove both
left Quillen fields for the named Kan–Quillen and Joyal models. Native right
adjoint preservation then makes the literal k right image of a quasicategory Kan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra Limits MorphismProperty

namespace SSet.FreeGroupoidSimplex

/-- The original k left functor followed by the canonical Joyal designation. -/
def kLeft : SSet.{u} ⥤ JoyalSSet.{u} :=
  kFunctor.{u} ⋙ JoyalSSet.ofSSet.{u}

/-- Forget the Joyal designation before applying the original k right functor. -/
def kRight : JoyalSSet.{u} ⥤ SSet.{u} :=
  JoyalSSet.forget.{u} ⋙ kRightFunctor.{u}

/-- Compose the original k adjunction with the actual carrier adjunction. -/
def kWrappedAdjunction : kLeft.{u} ⊣ kRight.{u} :=
  kAdjunction.{u}.comp JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction

/-- The wrapped k adjunction is Quillen from the named Kan–Quillen model to the
named Joyal model, with neither model nor preservation supplied as a premise. -/
theorem kWrappedAdjunction_isQuillenAdjunction :
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    kWrappedAdjunction.{u}.IsQuillenAdjunction := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  have hCof : PreservesCofibrations kLeft.{u} := by
    intro X Y f hf
    let _ : Cofibration f := (HomotopicalAlgebra.cofibration_iff f).2 hf
    let _ : Mono f := SSet.modelCategoryQuillen.mono_of_cofibration f
    let _ : Mono (kFunctor.map f) := inferInstance
    change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations (kLeft.map f)
    rw [JoyalSSet.modelCategory_cofibrations]
    change Mono (JoyalSSet.ofSSet.map (kFunctor.map f))
    infer_instance
  refine ⟨hCof, ?_⟩
  intro X Y f hf
  have hsource := (HomotopicalAlgebra.mem_trivialCofibrations_iff f).1 hf
  have hw : realizationWeakEquivalences f :=
    (HomotopicalAlgebra.weakEquivalence_iff f).1 hsource.2
  refine ⟨hCof f hf.1, ?_⟩
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences (kLeft.map f)
  rw [JoyalSSet.modelCategory_weakEquivalences]
  change categoricalEquivalences (kFunctor.map f)
  exact (categoricalEquivalences_kFunctor_map_iff f).2 hw

/-- The literal original k right image of every quasicategory is Kan. -/
theorem kRightFunctor_kanComplex_of_quasicategory (Q : SSet.{u}) [Quasicategory Q] :
    KanComplex (kRightFunctor.obj Q) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : kWrappedAdjunction.{u}.IsQuillenAdjunction :=
    kWrappedAdjunction_isQuillenAdjunction
  have hterminal : IsTerminal (JoyalSSet.ofSSet.obj (⊤_ SSet.{u})) :=
    terminalIsTerminal.isTerminalObj JoyalSSet.ofSSet (⊤_ SSet.{u})
  have hp : Fibration (JoyalSSet.ofSSet.map (terminal.from Q)) := by
    rw [HomotopicalAlgebra.fibration_iff]
    change JoyalSSet.modelCategory.categoryWithFibrations.fibrations
      (JoyalSSet.ofSSet.map (terminal.from Q))
    rw [JoyalSSet.modelCategory_fibrations]
    change categoricalFibrations (terminal.from Q)
    exact (categoricalFibrations.terminalFrom_iff_quasicategory Q).2 inferInstance
  have hQ : IsFibrant (JoyalSSet.ofSSet.obj Q) :=
    (isFibrant_iff_of_isTerminal (JoyalSSet.ofSSet.map (terminal.from Q)) hterminal).2 hp
  exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := kWrappedAdjunction)).isFibrant hQ

end SSet.FreeGroupoidSimplex
