/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceIso

/-!
# The genuine original native full-boundary latching attachment

The same root-boundary chart is the colimit of every original full
native face and intersection through its genuine source isomorphism.
Its actual free-root pushout therefore proves the projective left
class of the original whole boundary attaching map. The same map and
the original physical straightened inclusion are cofibrations in the
actual coherent marked model, with all original bases and marks kept.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The unchanged original all-face cocone is isomorphic to the same actual root-boundary cocone through its genuine
whole source comparison, retaining every original face leg. -/
def nativeBoundaryRootFaceCoconeIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeBoundaryFaceChartCocone B n σ ≅ nativeBoundaryRootFaceCocone B n σ :=
  Multicofork.ext (nativeBoundaryRootSourceIso B n σ) (nativeBoundaryRootSourceMap_leg B n σ)

/-- The same actual native root boundary is genuinely the colimit of all unchanged original full marked face charts
and pairwise intersections. -/
def nativeBoundaryRootFaceIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    IsColimit (nativeBoundaryRootFaceCocone B n σ) :=
  IsColimit.ofIsoColimit (nativeBoundaryFaceChartIsColimit B n σ) (nativeBoundaryRootFaceCoconeIso B n σ)

/-- The original actual whole boundary attaching map has the genuine projective left class through its same source
isomorphism and original free-root enriched pushout. -/
theorem nativeBoundaryChartMap_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (nativeBoundaryChartMap B (n + 1) σ) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  have h := G.rlp.llp.comp_mem (nativeBoundaryRootSourceMap B n σ)
    (nativeRootBoundaryChartMap B (n + 1) σ)
    (G.rlp.llp_of_isIso (nativeBoundaryRootSourceMap B n σ))
    (nativeRootBoundaryChartMap_projectiveLeft B (n + 1) σ)
  exact (nativeBoundaryRootSourceMap_attachment B n σ) ▸ h

/-- The unchanged original native full-boundary attaching map is monic as its same whole enriched map over every
original simplicial base. -/
instance nativeBoundaryChartMap_mono (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    Mono (nativeBoundaryChartMap B (n + 1) σ) :=
  coherentDiagram_projectiveLeft_mono B (nativeBoundaryChartMap B (n + 1) σ)
    (nativeBoundaryChartMap_projectiveLeft B n σ)

/-- The same unchanged actual whole-boundary attaching map is a cofibration in the genuinely constructed original
coherent marked model. -/
theorem nativeBoundaryChartMap_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration (nativeBoundaryChartMap B (n + 1) σ) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeBoundaryChartMap_projectiveLeft B n σ

/-- Straightening of the same physical original minimally marked boundary inclusion has the genuine projective left
class, with its original source and target retained. -/
theorem nativeBoundaryInclusion_straightening_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      ((nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1)))) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  let e := nativeSimplexImageIso B (n + 1) σ
  let f := (nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1)))
  have h := G.rlp.llp.comp_mem (nativeBoundaryChartMap B (n + 1) σ) e.inv
    (nativeBoundaryChartMap_projectiveLeft B n σ) (G.rlp.llp_of_isIso e.inv)
  have he : nativeBoundaryChartMap B (n + 1) σ ≫ e.inv = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => f ≫ q) e.hom_inv_id).trans (Category.comp_id f))
  change G.rlp.llp f
  exact he ▸ h

/-- The same physical original minimally marked boundary inclusion is sent by actual native straightening to a
cofibration in the original coherent marked model. -/
theorem nativeBoundaryInclusion_straightening_cofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration ((nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1)))) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeBoundaryInclusion_straightening_projectiveLeft B n σ

end SSet.Marked
