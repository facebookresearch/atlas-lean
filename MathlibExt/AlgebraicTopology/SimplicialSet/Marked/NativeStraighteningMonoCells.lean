/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingImage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryAllDimensions

/-!
# Every actual original marked mono generator straightens cofibrantly

Each original target map to the fixed base is its actual whole Yoneda
representative. Identity marked carriers identify the original lifted
boundary or marking cell with its same native physical inclusion.
The actual all-dimensional boundary and sharp marking-cell proofs
therefore give the projective left class on every original generator.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Each actual whole original base projection identifies its original lifted boundary cell with the same original
native physical boundary inclusion, retaining both complete marked carriers. -/
def nativeBoundaryMonoCellArrowIso (B : SSet.{u}) (n : ℕ) (p : min (Δ[n] : SSet.{u}) ⟶ max B) :
    Arrow.mk (overCell monoCell.{u} (max B) ⟨Sum.inl n, p⟩) ≅
      Arrow.mk (nativeSubcomplexInclusion B n (SSet.yonedaEquiv p.hom) (boundary n)) := by
  let q : (Δ[n] : SSet.{u}) ⟶ B := p.hom
  have hq : SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q := SSet.yonedaEquiv.symm_apply_apply q
  let X : Over.mk (boundaryCell n ≫ p) ≅ nativeSubcomplexBasis B n (SSet.yonedaEquiv p.hom) (boundary n) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (boundary n : SSet.{u})) ≫ ((boundary n).ι ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q)) =
        (boundary n).ι ≫ q
      exact (Category.id_comp _).trans (congrArg (fun f => (boundary n).ι ≫ f) hq))
  let Y : Over.mk p ≅ nativeSimplexBasis B n (SSet.yonedaEquiv p.hom) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q
      exact (Category.id_comp _).trans hq)
  exact Arrow.isoMk X Y (by
    apply Over.OverMorphism.ext
    apply Hom.ext
    ext q x
    rfl)

/-- Each actual whole original sharp target projection identifies its original lifted marking cell with the same
physical native marking cell through unchanged marked identity carriers. -/
def nativeMarkingMonoCellArrowIso (B : SSet.{u}) (p : max (Δ[1] : SSet.{u}) ⟶ max B) :
    Arrow.mk (overCell monoCell.{u} (max B) ⟨Sum.inr (), p⟩) ≅
      Arrow.mk (nativeMarkingCell B (SSet.yonedaEquiv p.hom)) := by
  let q : (Δ[1] : SSet.{u}) ⟶ B := p.hom
  have hq : SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q := SSet.yonedaEquiv.symm_apply_apply q
  let X : Over.mk (edgeMarkCell ≫ p) ≅ nativeSimplexBasis B 1 (SSet.yonedaEquiv p.hom) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (Δ[1] : SSet.{u})) ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = (𝟙 (Δ[1] : SSet.{u})) ≫ q
      exact congrArg (fun f => (𝟙 (Δ[1] : SSet.{u})) ≫ f) hq)
  let Y : Over.mk p ≅ nativeSharpBasis B (SSet.yonedaEquiv p.hom) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (Δ[1] : SSet.{u})) ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q
      exact (Category.id_comp _).trans hq)
  exact Arrow.isoMk X Y (by
    apply Over.OverMorphism.ext
    apply Hom.ext
    ext q x
    rfl)

/-- Every actual original marked boundary or marking generator over each whole original base map straightens into
the genuine projective left class on the same original coherent diagram model. -/
theorem nativeStraightening_monoCells_projectiveLeft (B : SSet.{u}) :
    overCells monoCell.{u} (max B) ≤
      ((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp).inverseImage
        (nativeStraightening B) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  let P := G.rlp.llp.inverseImage (nativeStraightening B)
  apply (ofHoms_le_iff (overCell monoCell.{u} (max B)) P).mpr
  rintro ⟨(n | tag), p⟩
  · exact (P.arrow_iso_iff (nativeBoundaryMonoCellArrowIso B n p)).mpr
      (nativeBoundaryInclusion_straightening_all_projectiveLeft B n (SSet.yonedaEquiv p.hom))
  · cases tag
    exact (P.arrow_iso_iff (nativeMarkingMonoCellArrowIso B p)).mpr
      (nativeMarkingCell_straightening_projectiveLeft B (SSet.yonedaEquiv p.hom))

end SSet.Marked
