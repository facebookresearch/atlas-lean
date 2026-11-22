/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentSharpIntervalEndpointPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeTailFaceMate
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingImage

/-!
# The SAME ORIGINAL native marked Cartesian endpoint weak image

The genuine original sharp interval endpoint pushout left-extends over
the unchanged whole original base edge. The actual full zeroth-face
Source Iso and sharp interval unit mate retain the SAME physical marked
endpoint attaching arrow. Its actual weak projective class therefore
belongs to straightening every original marked endpoint over every
original whole base projection, including arbitrary non-Kan bases.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The SAME full original sharp interval endpoint chart map is its actual native enriched left extension. -/
def nativeSharpCartesianEndpointChartMap (B : SSet.{u}) (σ : B _⦋1⦌) :
    nativePositiveRootChart B 1 σ ⟶ nativeSharpChart B σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map coneSharpEndpointDiagramMap

/-- The actual original endpoint chart map keeps precisely its whole original positive cone and sharp marking
factors. -/
theorem nativeSharpCartesianEndpointChartMap_factors (B : SSet.{u}) (σ : B _⦋1⦌) :
    nativeSharpCartesianEndpointChartMap B σ = nativePositiveRootChartMap B 1 σ ≫ nativeSharpMarkingChartMap B σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map_comp
    (coneAfterDiagramInclusion (⊥ : Vertex.{u} 1)) (coneSharp 1)

/-- The SAME entire original marked endpoint chart retains the actual zeroth-face Source Iso and whole original
simplex restriction. -/
theorem nativeSharpCartesianEndpointChartMap_source (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeTailFaceSourceIso B 0 σ).hom ≫ nativeSharpCartesianEndpointChartMap B σ =
      nativeSimplexChartRestriction B (SimplexCategory.δ (0 : Fin 2)) σ ≫ nativeSharpMarkingChartMap B σ := by
  have h₀ := congrArg (fun f => (nativeTailFaceSourceIso B 0 σ).hom ≫ f)
    (nativeSharpCartesianEndpointChartMap_factors B σ)
  have h₁ := (Category.assoc (nativeTailFaceSourceIso B 0 σ).hom
    (nativePositiveRootChartMap B 1 σ) (nativeSharpMarkingChartMap B σ)).symm
  have h₂ := congrArg (fun f => f ≫ nativeSharpMarkingChartMap B σ) (nativeTailFaceSourceIso_attachment B 0 σ)
  exact h₀.trans (h₁.trans h₂)

/-- The SAME whole original marked endpoint chart has its genuine native weak projective left class through the
actual original enriched pushout. -/
theorem nativeSharpCartesianEndpointChartMap_projectiveWeakLeft (B : SSet.{u}) (σ : B _⦋1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (nativeSharpCartesianEndpointChartMap B σ) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingWeakMonos
    coneSharpEndpointDiagramMap coneSharpEndpointDiagramMap_projectiveWeakLeft

/-- The original whole physical marked Cartesian endpoint over its actual unchanged native base-edge records. -/
def nativeCartesianEndpointCell (B : SSet.{u}) (σ : B _⦋1⦌) :
    nativeSimplexBasis B 0 (B.map (SimplexCategory.δ (0 : Fin 2)).op σ) ⟶ nativeSharpBasis B σ :=
  nativeSimplexRestriction B (SimplexCategory.δ (0 : Fin 2)) σ ≫ nativeMarkingCell B σ

/-- The SAME physical original endpoint native image retains BOTH its actual point Source Iso and sharp Target Iso. -/
theorem nativeCartesianEndpointCell_image (B : SSet.{u}) (σ : B _⦋1⦌) :
    ((nativeSimplexImageIso B 0 (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom ≫
      (nativeTailFaceSourceIso B 0 σ).hom) ≫ nativeSharpCartesianEndpointChartMap B σ =
    (nativeStraightening B).map (nativeCartesianEndpointCell B σ) ≫ (nativeSharpImageIso B σ).hom := by
  let S := nativeStraightening B
  let e := nativeSimplexImageIso B 0 (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)
  let r := nativeSimplexRestriction B (SimplexCategory.δ (0 : Fin 2)) σ
  let m := nativeMarkingCell B σ
  let a := nativeSharpMarkingChartMap B σ
  let d := nativeSharpImageIso B σ
  have h₀ := Category.assoc e.hom (nativeTailFaceSourceIso B 0 σ).hom (nativeSharpCartesianEndpointChartMap B σ)
  have h₁ := congrArg (fun f => e.hom ≫ f) (nativeSharpCartesianEndpointChartMap_source B σ)
  have h₂ := (Category.assoc e.hom (nativeSimplexChartRestriction B (SimplexCategory.δ (0 : Fin 2)) σ) a).symm
  have h₃ := congrArg (fun f => f ≫ a) (nativeSimplexChartRestriction_square B (SimplexCategory.δ (0 : Fin 2)) σ)
  have h₄ := Category.assoc (S.map r) (nativeSimplexImageIso B 1 σ).hom a
  have h₅ := congrArg (fun f => S.map r ≫ f) (nativeMarkingCell_straightening_image B σ).symm
  have h₆ := (Category.assoc (S.map r) (S.map m) d.hom).symm
  have h₇ := congrArg (fun f => f ≫ d.hom) (S.map_comp r m).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))))

/-- Both SAME entire original endpoint attaching arrows are genuinely isomorphic through their original full marked
source and target maps. -/
def nativeCartesianEndpointCellImageArrowIso (B : SSet.{u}) (σ : B _⦋1⦌) :
    Arrow.mk ((nativeStraightening B).map (nativeCartesianEndpointCell B σ)) ≅
      Arrow.mk (nativeSharpCartesianEndpointChartMap B σ) :=
  Arrow.isoMk
    (nativeSimplexImageIso B 0 (B.map (SimplexCategory.δ (0 : Fin 2)).op σ) ≪≫ nativeTailFaceSourceIso B 0 σ)
    (nativeSharpImageIso B σ) (nativeCartesianEndpointCell_image B σ)

/-- The SAME physical original native marked endpoint has the actual weak projective left class over every arbitrary
base edge. -/
theorem nativeCartesianEndpointCell_straightening_projectiveWeakLeft (B : SSet.{u}) (σ : B _⦋1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (nativeCartesianEndpointCell B σ)) :=
  (((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp).arrow_iso_iff
    (nativeCartesianEndpointCellImageArrowIso B σ)).mpr (nativeSharpCartesianEndpointChartMap_projectiveWeakLeft B σ)

/-- Every original whole marked target-to-base map retains the SAME physical Cartesian endpoint slice arrow through
marked carrier identities. -/
def nativeOriginalCartesianEndpointOverArrowIso (B : SSet.{u}) (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    Arrow.mk (cartesianEndpointOver r) ≅ Arrow.mk (nativeCartesianEndpointCell B (SSet.yonedaEquiv r.hom)) := by
  let σ := SSet.yonedaEquiv r.hom
  let δ := SimplexCategory.δ (0 : Fin 2)
  have hq : SSet.yonedaEquiv.symm σ = r.hom := Equiv.symm_apply_apply SSet.yonedaEquiv r.hom
  have hp : SSet.stdSimplex.map δ ≫ SSet.yonedaEquiv.symm σ =
      SSet.yonedaEquiv.symm (B.map δ.op σ) := congrArg Hom.hom (Over.w (nativeSimplexRestriction B δ σ))
  let X : Over.mk (cartesianEndpointCell ≫ r) ≅ nativeSimplexBasis B 0 (B.map δ.op σ) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change 𝟙 (Δ[0] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (B.map δ.op σ) = SSet.stdSimplex.map δ ≫ r.hom
      exact (Category.id_comp _).trans (hp.symm.trans (congrArg (fun f => SSet.stdSimplex.map δ ≫ f) hq)))
  let Y : Over.mk r ≅ nativeSharpBasis B σ := Over.isoMk (Iso.refl _) (Hom.ext ((Category.id_comp _).trans hq))
  exact Arrow.isoMk X Y (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)

/-- Straightening EVERY SAME original Cartesian endpoint over EVERY whole original marked base projection has its
genuine weak projective image. -/
theorem nativeOriginalCartesianEndpointOver_straightening_projectiveWeakLeft (B : SSet.{u})
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (cartesianEndpointOver r)) := by
  let P := ((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp).inverseImage
    (nativeStraightening B)
  exact (P.arrow_iso_iff (nativeOriginalCartesianEndpointOverArrowIso B r)).mpr
    (nativeCartesianEndpointCell_straightening_projectiveWeakLeft B (SSet.yonedaEquiv r.hom))

/-- The SAME whole ORIGINAL physical Cartesian endpoint native image is genuinely a trivial cofibration in the
actual coherent marked model, including arbitrary non-Kan bases. -/
theorem nativeOriginalCartesianEndpointOver_straightening_trivialCofibration (B : SSet.{u})
    (r : max (Δ[1] : SSet.{u}) ⟶ max B) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) ((nativeStraightening B).map (cartesianEndpointOver r))
      := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeOriginalCartesianEndpointOver_straightening_projectiveWeakLeft B r

end SSet.Marked
