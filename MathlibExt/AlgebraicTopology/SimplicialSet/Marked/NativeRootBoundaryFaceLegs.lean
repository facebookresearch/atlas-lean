/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeProperBoundaryFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryMonomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeFaceChartIso

/-!
# The original whole boundary face legs into the actual root boundary

The original full scalar face chart is identified with its native
restricted simplex by the same minimal face isomorphism and unit
mate. Its inverse followed by the proved proper-face map gives the
actual supported face leg. Its attaching composite is the original
whole relative chart inclusion, with every original mark retained.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same original full native single-face chart comparison preserves its actual attaching map into the original
full simplex chart. -/
theorem nativeSingleFaceChartIso_attachment (B : SSet.{u}) (n : ℕ)
    (i : Fin (n + 2)) (σ : B _⦋n + 1⦌) :
    (nativeSingleFaceChartIso B n i σ).hom ≫
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) =
      nativeSimplexChartRestriction B (SimplexCategory.δ i) σ := by
  let T := nativeStraightening B
  let e := nativeSimplexImageIso B n (B.map (SimplexCategory.δ i).op σ)
  let d := nativeSimplexImageIso B (n + 1) σ
  let f := (nativeSingleFaceBasisIso B n i σ).hom
  let g := nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ)
  have hfg : f ≫ g = nativeSimplexRestriction B (SimplexCategory.δ i) σ :=
    nativeSingleFaceBasisIso_inclusion B n i σ
  have hm : T.map f ≫ T.map g = T.map (nativeSimplexRestriction B (SimplexCategory.δ i) σ) :=
    (T.map_comp f g).symm.trans (congrArg T.map hfg)
  change (e.inv ≫ T.map f) ≫ (T.map g ≫ d.hom) =
    (e.inv ≫ T.map (nativeSimplexRestriction B (SimplexCategory.δ i) σ)) ≫ d.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.inv ≫ v) (Category.assoc (T.map f) (T.map g) d.hom).symm).trans
      ((congrArg (fun v => e.inv ≫ (v ≫ d.hom)) hm).trans (Category.assoc _ _ _).symm))

/-- Each original full scalar face chart enters the actual supported boundary by its unchanged native face
comparison and proper-face unit mate. -/
def nativeBoundaryFaceToRoot (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeSubcomplexChart B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) ⟶
      nativeRootBoundaryChart B (n + 1) σ :=
  (nativeSingleFaceChartIso B n i σ).inv ≫ nativeRootBoundaryCofaceMap B n σ i

/-- Every original full face leg keeps precisely the unchanged original relative face attaching map. -/
theorem nativeBoundaryFaceToRoot_attachment (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeBoundaryFaceToRoot B n σ i ≫ nativeRootBoundaryChartMap B (n + 1) σ =
      nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ) := by
  let e := nativeSingleFaceChartIso B n i σ
  have hf := nativeRootBoundaryCofaceMap_attachment B n σ i
  have hg := nativeSingleFaceChartIso_attachment B n i σ
  change (e.inv ≫ nativeRootBoundaryCofaceMap B n σ i) ≫ nativeRootBoundaryChartMap B (n + 1) σ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.inv ≫ v) hf).trans
      ((congrArg (fun v => e.inv ≫ v) hg.symm).trans
        (e.inv_hom_id_assoc (nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i}ᶜ)))))

end SSet.Marked
