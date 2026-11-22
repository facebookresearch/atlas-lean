/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryZeroRootSource

/-!
# Actual original native boundary sources and cofibrations in all dimensions

The genuine original empty source in dimension zero and genuine full
face/intersection source in every positive dimension give one actual
root-boundary source isomorphism. The forward map in every positive
dimension is precisely the original all-face comparison. The unchanged
whole attaching map and its physical straightened original minimally
marked inclusion have the actual projective left class and coherent
model cofibration in every dimension over every original base.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual original native simplex boundary is the same whole original root-boundary chart in every dimension,
with its genuine original empty or full-face source comparison. -/
def nativeBoundaryFullRootSourceIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativeSubcomplexChart B n σ (boundary n) ≅ nativeRootBoundaryChart B n σ :=
  match n, σ with
  | 0, σ => nativeBoundaryZeroRootSourceIso B σ
  | n + 1, σ => nativeBoundaryRootSourceIso B n σ

/-- In every positive original dimension, the whole source isomorphism has precisely the unchanged original all-face
comparison as its forward map. -/
theorem nativeBoundaryFullRootSourceIso_succ_hom (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeBoundaryFullRootSourceIso B (n + 1) σ).hom = nativeBoundaryRootSourceMap B n σ := rfl

/-- The same full source isomorphism retains exactly the original native whole-boundary attaching map in every
original dimension. -/
theorem nativeBoundaryFullRootSourceIso_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (nativeBoundaryFullRootSourceIso B n σ).hom ≫ nativeRootBoundaryChartMap B n σ =
      nativeBoundaryChartMap B n σ := by
  cases n with
  | zero => exact nativeBoundaryZeroRootSourceIso_attachment B σ
  | succ n => exact nativeBoundaryRootSourceIso_attachment B n σ

/-- The unchanged original whole native boundary attaching map has the genuine projective left class in every
original dimension and universe over every original simplicial base. -/
theorem nativeBoundaryChartMap_all_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp (nativeBoundaryChartMap B n σ) := by
  cases n with
  | zero => exact nativeBoundaryZeroChartMap_projectiveLeft B σ
  | succ n => exact nativeBoundaryChartMap_projectiveLeft B n σ

/-- The same actual full original native boundary attaching map is monic in every original dimension. -/
instance nativeBoundaryChartMap_all_mono (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    Mono (nativeBoundaryChartMap B n σ) :=
  coherentDiagram_projectiveLeft_mono B (nativeBoundaryChartMap B n σ) (nativeBoundaryChartMap_all_projectiveLeft B n σ)

/-- The same original whole native boundary attaching map is a cofibration in the actual original coherent marked
model in every original dimension. -/
theorem nativeBoundaryChartMap_all_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration (nativeBoundaryChartMap B n σ) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeBoundaryChartMap_all_projectiveLeft B n σ

/-- Actual native straightening of the same physical original minimally marked boundary inclusion has the genuine
projective left class in every original dimension. -/
theorem nativeBoundaryInclusion_straightening_all_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      ((nativeStraightening B).map (nativeSubcomplexInclusion B n σ (boundary n))) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  let e := nativeSimplexImageIso B n σ
  let f := (nativeStraightening B).map (nativeSubcomplexInclusion B n σ (boundary n))
  have h := G.rlp.llp.comp_mem (nativeBoundaryChartMap B n σ) e.inv
    (nativeBoundaryChartMap_all_projectiveLeft B n σ) (G.rlp.llp_of_isIso e.inv)
  have he : nativeBoundaryChartMap B n σ ≫ e.inv = f :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => f ≫ q) e.hom_inv_id).trans (Category.comp_id f))
  change G.rlp.llp f
  exact he ▸ h

/-- Actual native straightening of the same physical original minimally marked boundary inclusion is a cofibration
in the actual original coherent marked model in every original dimension. -/
theorem nativeBoundaryInclusion_straightening_all_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration ((nativeStraightening B).map (nativeSubcomplexInclusion B n σ (boundary n))) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeBoundaryInclusion_straightening_all_projectiveLeft B n σ

end SSet.Marked
