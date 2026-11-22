/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundaryCountablePiecePresentability
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableIntervalReadback
import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# An actual small original family of countable cofibrant weak two-label intervals

The genuine original fixed-label local presentability supplies a small
up-to-isomorphism class of ℵ₁-presentable objects. Restricting to the
proved original countable, fixed-cofibrant, weak-unit intervals gives
actual small representatives within the SAME class. Every constructed
original equivalence interval has a full fixed-label isomorphism to
one of those actual representatives. No model or A2 lift is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects OriginalWalkingArrowFreeSingleHomIso OriginalBoundaryGoodTree
attribute [local instance] FixedObjectModel.modelCategory

/-- The precise genuine original interval property on the SAME two-label fixed-object category. -/
def intervals : ObjectProperty (FixedObjects walking.{u}) := fun H =>
  IsCardinalPresentable H rank.{u} ∧ CountableHoms H ∧ IsCofibrant H ∧
    FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H)

/-- These genuine original intervals are essentially small in the SAME coefficient universe. -/
instance intervals_essentiallySmall : ObjectProperty.EssentiallySmall.{u} intervals.{u} :=
  ObjectProperty.EssentiallySmall.of_le (fun _ h => h.1)

/-- The actual small original representative property, with every representative itself a genuine original interval. -/
def representatives : ObjectProperty (FixedObjects walking.{u}) :=
  (ObjectProperty.EssentiallySmall.exists_small_le intervals.{u}).choose

/-- The SAME full representative carrier is small in the original coefficient universe. -/
instance representatives_small : ObjectProperty.Small.{u} representatives.{u} :=
  (ObjectProperty.EssentiallySmall.exists_small_le intervals.{u}).choose_spec.choose

/-- Every actual chosen representative retains the complete genuine original interval hypotheses. -/
theorem representative_interval (H : FixedObjects walking.{u}) (hH : representatives H) : intervals H :=
  (ObjectProperty.EssentiallySmall.exists_small_le intervals.{u}).choose_spec.choose_spec.1 H hH

/-- Every genuine original interval is related by a full fixed-label isomorphism to a SAME actual representative. -/
theorem represented (H : FixedObjects walking.{u}) (hH : intervals H) :
    ∃ K : FixedObjects walking, representatives K ∧ Nonempty (K ≅ H) := by
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    (ObjectProperty.EssentiallySmall.exists_small_le intervals.{u}).choose_spec.choose_spec.2 H hH
  exact ⟨K, hK, ⟨e.symm⟩⟩

variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- The actual constructed arbitrary-equivalence interval satisfies the entire genuine original property. -/
theorem original_interval : intervals (OriginalEquivalenceCountableInterval.fixedObject a e he) :=
  ⟨OriginalEquivalenceCountableInterval.presentable a e he, inferInstance,
    OriginalEquivalenceCountableInterval.isCofibrant a e he,
    OriginalEquivalenceCountableInterval.terminal_weak a e he⟩

/-- Every SAME supplied original equivalence therefore has an actual full original representative isomorphism. -/
theorem original_represented :
    ∃ K : FixedObjects walking, representatives K ∧
      Nonempty (K ≅ OriginalEquivalenceCountableInterval.fixedObject a e he) :=
  represented _ (original_interval a e he)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
