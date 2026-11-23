/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceNaturalMap

/-!
# The cokernel map to a horizontal graded piece

The natural-stage zero-composite theorem is transported back to the complete
filtration.  This gives, uniformly in the zeroth and positive columns, a
projection whose composite with `F_{p-1} → F_p` is zero and hence a canonical
map from the cokernel to the direct shifted-column presentation.

The following splitting and cokernel-isomorphism modules prove that this map
is an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

noncomputable def horizontalNaturalStageCochainIso (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left ≅
      (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    (eqToIso (horizontalTotalFiltration_diagram_obj K p))

set_option linter.flexible false in
theorem horizontalNaturalStageCochainIso_naturality
    {p r : ℕ} (h : p ≤ r) :
    (ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map (homOfLE h)).hom.left ≫
        (horizontalNaturalStageCochainIso K r).hom =
      (horizontalNaturalStageCochainIso K p).hom ≫
        (ComplexShape.embeddingDownNat.extendFunctor C).map
          (horizontalFilteredTotalComplexMap K h) := by
  ext i
  simp [horizontalNaturalStageCochainIso]
  have hmap := horizontalTotalFiltration_diagram_map K h
  change ((horizontalTotalFiltration K).toMonoOver.map
      (homOfLE h)).hom.left = horizontalFilteredTotalComplexMap K h at hmap
  exact congrArg
    (fun f => ((ComplexShape.embeddingDownNat.extendFunctor C).map f).f i) hmap

noncomputable def horizontalMonoStageDirectColumnProjectionMap (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left ⟶
      horizontalDirectColumnCochain K p :=
  (horizontalNaturalStageCochainIso K p).hom ≫
    horizontalNaturalDirectColumnProjectionMap K p

theorem horizontalMonoStageDirectColumnProjectionMap_stageMap_zero (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p))).hom.left ≫
      horizontalMonoStageDirectColumnProjectionMap K (p + 1) = 0 := by
  unfold horizontalMonoStageDirectColumnProjectionMap
  rw [← Category.assoc, horizontalNaturalStageCochainIso_naturality]
  rw [Category.assoc, horizontalNaturalDirectColumnProjectionMap_stageMap_zero,
    comp_zero]

noncomputable def horizontalCompleteSuccDirectColumnProjectionMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) ⟶
      horizontalDirectColumnCochain K (p + 1) :=
  (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom ≫
    horizontalMonoStageDirectColumnProjectionMap K (p + 1)

theorem horizontalFirstPageFiltrationMap_succ_projection_zero (p : ℕ) :
    horizontalFirstPageFiltrationMap K (p + 1) ≫
      horizontalCompleteSuccDirectColumnProjectionMap K p = 0 := by
  unfold horizontalCompleteSuccDirectColumnProjectionMap
  rw [← Category.assoc, horizontalFirstPageFiltrationMap_succ_monoIso]
  rw [Category.assoc, horizontalMonoStageDirectColumnProjectionMap_stageMap_zero,
    comp_zero]

/-- Projection of the complete upper filtration stage onto column `p`. -/
noncomputable def horizontalCompleteDirectColumnProjectionMap :
    (p : ℕ) →
      (horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p) ⟶
        horizontalDirectColumnCochain K p
  | 0 => horizontalDirectColumnProjectionMap K 0
  | p + 1 => horizontalCompleteSuccDirectColumnProjectionMap K p

theorem horizontalFirstPageFiltrationMap_projection_zero (p : ℕ) :
    horizontalFirstPageFiltrationMap K p ≫
      horizontalCompleteDirectColumnProjectionMap K p = 0 := by
  cases p with
  | zero => exact horizontalFirstPageFiltrationMap_zero_projection K
  | succ p => exact horizontalFirstPageFiltrationMap_succ_projection_zero K p

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Canonical map from the consecutive-stage cokernel to the `p`th direct
column presentation. -/
noncomputable def horizontalFirstPageCokernelToDirectColumn (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  cokernel.desc (horizontalFirstPageFiltrationMap K p)
    (horizontalCompleteDirectColumnProjectionMap K p)
    (horizontalFirstPageFiltrationMap_projection_zero K p)

end HomologicalComplex₂

end
