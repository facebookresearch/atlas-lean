/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentComposition
import MathlibExt.AlgebraicTopology.RelativeCellComplex.OriginalAttachCellsFiniteColimit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerRootWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerGeneratingCobaseAcyclicity

/-!
# Every full original simultaneous A1/A2 attachment is genuinely weak

All actual original occurrences and their complete coproducts are
retained. The finite original subfamilies have genuine original
single-cell insertion pushouts; their full under-root colimit is the
same supplied original AttachCells target. Original full-Hom filtered
weakness therefore proves weakness of the same simultaneous map.

The cell-occurrence universe is independent and explicitly bounded by
the original coefficient universe. No fibrancy or source cofibrancy
premise is imposed.
-/

noncomputable section
universe u v w
open CategoryTheory Limits HomotopicalAlgebra Classical
attribute [local instance] IsFiltered.isConnected

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- Every actual finite subfamily of an original A1/A2 attachment has genuine C0 and DK-weak insertion maps. -/
theorem occurrenceMap_pushouts_le_cofibration_weak
    {α : Type w} {A B : α → Carrier.{u}} {g : ∀ i, A i ⟶ B i}
    {C D : Carrier.{u}} {f : C ⟶ D} (c : AttachCells.{v} g f)
    (hg : ∀ i, generatingTrivialCofibrations (g i)) :
    (MorphismProperty.ofHoms c.occurrenceMap).pushouts ≤
      Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  rintro X Y q ⟨A', B', p, a, b, ⟨i⟩, sq⟩
  exact generatingTrivialCofibrations_pushouts_le_cofibration_weak q
    ⟨_, _, _, a, b, hg (c.π i), sq⟩

/-- The SAME full original simultaneous attachment is DK weak for arbitrary original A1/A2 occurrences. -/
theorem attachCells_weak [UnivLE.{v, u}]
    {α : Type w} {A B : α → Carrier.{u}} {g : ∀ i, A i ⟶ B i}
    {C D : Carrier.{u}} {f : C ⟶ D} (c : AttachCells.{v} g f)
    (hg : ∀ i, generatingTrivialCofibrations (g i)) :
    EnrichedDwyerKan.weakEquivalences f := by
  let _ : HasColimitsOfSize.{v, v} Carrier.{u} :=
    hasColimitsOfSizeOfUnivLE.{u, u, v, v} Carrier.{u}
  let P : MorphismProperty Carrier.{u} :=
    Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences
  have hP : (MorphismProperty.ofHoms c.occurrenceMap).pushouts ≤ P :=
    occurrenceMap_pushouts_le_cofibration_weak c hg
  have hC : ∀ {s t : Finset c.ι} (h : s ⟶ t),
      Bergner.cofibrations (c.finiteDiagram.map h).right := by
    intro s t h
    exact (FinitePartialAttachment.map_mem c.occurrenceMap c.occurrenceAttaching
      P hP (leOfHom h)).1
  have hU : ∀ s : Finset c.ι, EnrichedDwyerKan.weakEquivalences
      (c.finiteDiagram.obj s).hom := by
    intro s
    exact (FinitePartialAttachment.root_mem c.occurrenceMap c.occurrenceAttaching P hP s).2
  exact OriginalFilteredRoot.weak_of_cofibrations.{u, v, v}
    c.finiteDiagram c.finiteCocone c.finiteIsColimit hC hU

/-- The SAME complete original simultaneous attachment is both C0 cofibrant and DK weak. -/
theorem attachCells_cofibration_weak [UnivLE.{v, u}]
    {α : Type w} {A B : α → Carrier.{u}} {g : ∀ i, A i ⟶ B i}
    {C D : Carrier.{u}} {f : C ⟶ D} (c : AttachCells.{v} g f)
    (hg : ∀ i, generatingTrivialCofibrations (g i)) :
    (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) f := by
  refine ⟨?_, attachCells_weak c hg⟩
  have h : MorphismProperty.ofHoms g ≤ Bergner.cofibrations := by
    rintro X Y q ⟨i⟩
    exact (generatingTrivialCofibrations_le_cofibration_weak _ (hg i)).1
  have hC : MorphismProperty.coproducts.{v} (MorphismProperty.ofHoms g) ≤
      Bergner.cofibrations :=
    le_trans (MorphismProperty.coproducts_monotone h) Bergner.cofibrations.coproducts_le
  have hF : (MorphismProperty.coproducts.{v} (MorphismProperty.ofHoms g)).pushouts ≤
      Bergner.cofibrations :=
    le_trans (MorphismProperty.pushouts_monotone hC) Bergner.cofibrations.pushouts_le
  exact hF _ c.pushouts_coproducts

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
