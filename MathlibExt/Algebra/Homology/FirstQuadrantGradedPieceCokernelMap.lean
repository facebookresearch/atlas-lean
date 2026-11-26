/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceNaturalMap

/-!
# Complete-filtration projection factors to direct columns

Let `K` be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. The extended natural filtration subobject identifies with the extended finite-
stage complex, compatibly with all stage inclusions.

Its direct-column projection vanishes on the preceding stage. Transporting this projection to
complete upper stages gives the same zero composite in both column zero and positive columns.
In an abelian category, the projection therefore factors through the categorical cokernel of
the consecutive-stage map.
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

/-- The finite-complex presentation of an extended natural filtration stage.

Identify the extended chain carrier of the natural filtration subobject with the cochain
extension of the finite filtered complex. -/
noncomputable def horizontalNaturalStageCochainIso (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left ≅
      (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    (eqToIso (horizontalTotalFiltration_diagram_obj K p))

set_option linter.flexible false in
/-- Naturality of finite-stage cochain presentations.

The natural filtration inclusion for `p ≤ r` commutes with the stage cochain isomorphisms and
the extended finite-stage map. -/
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

/-- The direct-column projection from an extended filtration subobject.

Use the natural-stage cochain comparison followed by projection from the extended finite stage
to its direct column. -/
noncomputable def horizontalMonoStageDirectColumnProjectionMap (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left ⟶
      horizontalDirectColumnCochain K p :=
  (horizontalNaturalStageCochainIso K p).hom ≫
    horizontalNaturalDirectColumnProjectionMap K p

/-- Vanishing of a preceding subobject stage under the new-column projection.

The extended inclusion of natural stage `p` into stage `p+1` followed by its direct-column
projection is zero. -/
theorem horizontalMonoStageDirectColumnProjectionMap_stageMap_zero (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p))).hom.left ≫
      horizontalMonoStageDirectColumnProjectionMap K (p + 1) = 0 := by
  unfold horizontalMonoStageDirectColumnProjectionMap
  rw [← Category.assoc, horizontalNaturalStageCochainIso_naturality]
  rw [Category.assoc, horizontalNaturalDirectColumnProjectionMap_stageMap_zero,
    comp_zero]

/-- The direct-column projection from a positive complete upper stage.

Transport the natural-stage projection through the upper-stage comparison for column `p+1`. -/
noncomputable def horizontalCompleteSuccDirectColumnProjectionMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) ⟶
      horizontalDirectColumnCochain K (p + 1) :=
  (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom ≫
    horizontalMonoStageDirectColumnProjectionMap K (p + 1)

/-- The zero composite for a positive complete filtration window.

The first-page filtration map for column `p+1` followed by its direct-column projection is
zero. -/
theorem horizontalFirstPageFiltrationMap_succ_projection_zero (p : ℕ) :
    horizontalFirstPageFiltrationMap K (p + 1) ≫
      horizontalCompleteSuccDirectColumnProjectionMap K p = 0 := by
  unfold horizontalCompleteSuccDirectColumnProjectionMap
  rw [← Category.assoc, horizontalFirstPageFiltrationMap_succ_monoIso]
  rw [Category.assoc, horizontalMonoStageDirectColumnProjectionMap_stageMap_zero,
    comp_zero]

/-- The complete upper-stage projection onto a direct column.

Use the direct projection for column zero and the positive upper-stage projection for column
`p+1`. -/
noncomputable def horizontalCompleteDirectColumnProjectionMap :
    (p : ℕ) →
      (horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p) ⟶
        horizontalDirectColumnCochain K p
  | 0 => horizontalDirectColumnProjectionMap K 0
  | p + 1 => horizontalCompleteSuccDirectColumnProjectionMap K p

/-- The zero composite of every complete column window with its projection.

For all `p ≥ 0`, the consecutive filtration map followed by the complete direct-column
projection is zero. -/
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

/-- The direct-column factor of a categorical filtration cokernel.

In an abelian category, the zero-composite projection descends to a map from the cokernel of
the first-page filtration map to the direct column. -/
noncomputable def horizontalFirstPageCokernelToDirectColumn (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  cokernel.desc (horizontalFirstPageFiltrationMap K p)
    (horizontalCompleteDirectColumnProjectionMap K p)
    (horizontalFirstPageFiltrationMap_projection_zero K p)

end HomologicalComplex₂

end
