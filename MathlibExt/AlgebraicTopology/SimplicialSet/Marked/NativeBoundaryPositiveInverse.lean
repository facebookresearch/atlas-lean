/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativePositiveRootBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceMap
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeTailFaceMate

/-!
# The actual all-face source inverse on the whole original positive chart

The genuine native zeroth-face source isomorphism gives the original
positive chart a map back to the actual simplex-boundary source.
The all-face source comparison recovers its unchanged positive chart
inclusion into the same complete root boundary. This is a whole marked
enriched identity, keeping all original base and unit maps. The root's
lower coordinate inverse charts remain to be constructed and glued.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The genuine original tail source comparison keeps the same full positive-chart inclusion into the actual
complete root boundary. -/
theorem nativeTailFaceSourceIso_rootBoundary (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeTailFaceSourceIso B n σ).hom ≫ nativePositiveRootBoundaryMap B (n + 1) σ =
      nativeRootBoundaryCofaceMap B n σ (0 : Fin (n + 2)) := by
  apply (cancel_mono (nativeRootBoundaryChartMap B (n + 1) σ)).mp
  have h₁ : ((nativeTailFaceSourceIso B n σ).hom ≫ nativePositiveRootBoundaryMap B (n + 1) σ) ≫
      nativeRootBoundaryChartMap B (n + 1) σ =
        (nativeTailFaceSourceIso B n σ).hom ≫ nativePositiveRootChartMap B (n + 1) σ :=
    (Category.assoc _ _ _).trans
      (congrArg (fun v => (nativeTailFaceSourceIso B n σ).hom ≫ v)
        (nativePositiveRootBoundaryMap_attachment B (n + 1) σ))
  exact h₁.trans ((nativeTailFaceSourceIso_attachment B n σ).trans
    (nativeRootBoundaryCofaceMap_attachment B n σ (0 : Fin (n + 2))).symm)

/-- The whole original positive chart maps back to the genuine all-face boundary source through its same tail source
inverse and original boundary coface injection. -/
def nativeBoundaryPositiveInverse (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativePositiveRootChart B (n + 1) σ ⟶
      nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) :=
  (nativeTailFaceSourceIso B n σ).inv ≫ nativeBoundaryCofaceChartMap B n σ (0 : Fin (n + 2))

/-- The actual all-face source comparison recovers the unchanged entire original positive chart inclusion from its
genuine positive-source inverse. -/
theorem nativeBoundaryPositiveInverse_source (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeBoundaryPositiveInverse B n σ ≫ nativeBoundaryRootSourceMap B n σ =
      nativePositiveRootBoundaryMap B (n + 1) σ := by
  let e := nativeTailFaceSourceIso B n σ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.inv ≫ v) (nativeBoundaryCofaceChartMap_root B n σ (0 : Fin (n + 2)))).trans
      ((congrArg (fun v => e.inv ≫ v) (nativeTailFaceSourceIso_rootBoundary B n σ).symm).trans
        (e.inv_hom_id_assoc (nativePositiveRootBoundaryMap B (n + 1) σ))))

/-- The whole original positive-source inverse retains exactly the same actual positive chart attaching map into the
full original simplex chart. -/
theorem nativeBoundaryPositiveInverse_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeBoundaryPositiveInverse B n σ ≫ nativeBoundaryChartMap B (n + 1) σ =
      nativePositiveRootChartMap B (n + 1) σ := by
  have hs := nativeBoundaryRootSourceMap_attachment B n σ
  have hp := nativeBoundaryPositiveInverse_source B n σ
  exact (congrArg (fun v => nativeBoundaryPositiveInverse B n σ ≫ v) hs.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun v => v ≫ nativeRootBoundaryChartMap B (n + 1) σ) hp).trans
        (nativePositiveRootBoundaryMap_attachment B (n + 1) σ)))

end SSet.Marked
