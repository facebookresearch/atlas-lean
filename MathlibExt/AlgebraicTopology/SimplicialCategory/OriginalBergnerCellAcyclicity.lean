/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerSimultaneousAttachmentWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalTransfiniteBergnerWeak
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Every original transfinite A1/A2 cell map is genuinely acyclic

The original simultaneous cell coproducts and all original well-order
stages are retained. Both the occurrence and stage universes are
independent and explicitly small. The genuine original source map is
C0 cofibrant and DK weak, including all original Hom maps and component
objects. This is cell acyclicity for the actual combined generators.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- All genuine original simultaneous A1/A2 coproduct pushouts are C0 cofibrant and DK weak. -/
theorem generatingTrivialCofibrations_coproducts_pushouts_le_cofibration_weak [UnivLE.{v, u}] :
    (MorphismProperty.coproducts.{v} generatingTrivialCofibrations.{u}).pushouts ≤
      Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  intro C D f hf
  have h : (MorphismProperty.coproducts.{v}
      (MorphismProperty.ofHoms generatingTrivialCofibrations.homFamily)).pushouts f := by
    simpa only [MorphismProperty.ofHoms_homFamily] using hf
  obtain ⟨c⟩ : Nonempty (AttachCells.{v} generatingTrivialCofibrations.homFamily f) :=
    (nonempty_attachCells_iff generatingTrivialCofibrations.homFamily f).mpr h
  exact attachCells_cofibration_weak c (fun i => i.2)

/-- The SAME original well-ordered combined-generator cell composite is C0 cofibrant and DK weak. -/
theorem generatingTrivialCofibrations_transfinite_cofibration_weak
    [UnivLE.{v, u}] [UnivLE.{w, u}]
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {C D : Carrier.{u}} {f : C ⟶ D}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (MorphismProperty.coproducts.{v} generatingTrivialCofibrations).pushouts J f) :
    (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) f := by
  let h' := h.ofLE
    generatingTrivialCofibrations_coproducts_pushouts_le_cofibration_weak.{u, v}
  exact ⟨Bergner.cofibrations.transfiniteCompositionsOfShape_le J f
    (h'.ofLE (by intro X Y q hq; exact hq.1)).mem,
      Bergner.weak_of_transfinite h'⟩

/-- Every SAME actual original relative A1/A2 cell complex is C0 cofibrant and DK weak. -/
theorem relativeCellComplex_cofibration_weak
    [UnivLE.{v, u}] [UnivLE.{w, u}]
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {α : J → Type t} {A B : (j : J) → α j → Carrier.{u}}
    (g : (j : J) → (i : α j) → A j i ⟶ B j i)
    {C D : Carrier.{u}} {f : C ⟶ D} (c : RelativeCellComplex.{v} g f)
    (hg : ∀ s : c.Cells, generatingTrivialCofibrations (g s.j s.i)) :
    (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) f :=
  generatingTrivialCofibrations_transfinite_cofibration_weak.{u, v, w}
    (c.transfiniteCompositionOfShape' hg)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
