/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryInverseCofaces

/-!
# The original native all-face boundary is the same root-boundary chart

Every original coface is recovered by the genuine full inverse. The
original boundary colimit, retaining every full marked face and pair
intersection, detects the remaining source identity. The resulting
isomorphism has exactly the original all-face comparison as its forward
map and exactly the constructed enriched inverse as its inverse; both
keep the original attaching maps and whole positive-chart entry.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire original native all-face boundary source identity is recovered by the same comparison and genuine
full inverse, detected by its original whole face/intersection colimit. -/
theorem nativeRootBoundaryChartInverse_boundary (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeBoundaryRootSourceMap B n σ ≫ nativeRootBoundaryChartInverse B n σ = 𝟙 _ := by
  apply Multicofork.IsColimit.hom_ext (nativeBoundaryFaceChartIsColimit B n σ)
  intro i
  let e := nativeSingleFaceChartIso B n i σ
  let π := (nativeBoundaryFaceChartCocone B n σ).π i
  let κ := nativeBoundaryRootSourceMap B n σ
  let β := nativeRootBoundaryChartInverse B n σ
  let q := nativeRootBoundaryCofaceMap B n σ i
  let c := nativeBoundaryCofaceChartMap B n σ i
  have h₁ : π ≫ (κ ≫ β) = (e.inv ≫ q) ≫ β :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ β) (nativeBoundaryRootSourceMap_leg B n σ i))
  have h₂ : (e.inv ≫ q) ≫ β = e.inv ≫ c :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => e.inv ≫ f) (nativeRootBoundaryChartInverse_coface B n σ i))
  exact h₁.trans (h₂.trans ((e.inv_hom_id_assoc π).trans (Category.comp_id π).symm))

/-- The actual native all-face boundary and actual root-coordinate boundary are isomorphic through their same
original comparison and genuine entire marked enriched inverse, in every universe and over every simplicial base. -/
def nativeBoundaryRootSourceIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) ≅ nativeRootBoundaryChart B (n + 1) σ where
  hom := nativeBoundaryRootSourceMap B n σ
  inv := nativeRootBoundaryChartInverse B n σ
  hom_inv_id := nativeRootBoundaryChartInverse_boundary B n σ
  inv_hom_id := nativeRootBoundaryChartInverse_source B n σ

/-- The full original source isomorphism has precisely the original whole boundary-colimit comparison as its forward
map. -/
theorem nativeBoundaryRootSourceIso_hom (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeBoundaryRootSourceIso B n σ).hom = nativeBoundaryRootSourceMap B n σ := rfl

/-- The full original source isomorphism has precisely the genuine native adjoint of the entire enriched inverse
section as its inverse. -/
theorem nativeBoundaryRootSourceIso_inv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeBoundaryRootSourceIso B n σ).inv = nativeRootBoundaryChartInverse B n σ := rfl

/-- The unchanged original all-face source comparison is genuinely an isomorphism. -/
instance nativeBoundaryRootSourceMap_isIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    IsIso (nativeBoundaryRootSourceMap B n σ) :=
  (nativeBoundaryRootSourceIso B n σ).isIso_hom

/-- The same original full source isomorphism retains every unchanged original native face leg. -/
theorem nativeBoundaryRootSourceIso_leg (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    (nativeBoundaryFaceChartCocone B n σ).π i ≫ (nativeBoundaryRootSourceIso B n σ).hom =
      nativeBoundaryFaceToRoot B n σ i :=
  nativeBoundaryRootSourceMap_leg B n σ i

/-- The same original full source isomorphism retains exactly the unchanged original native whole-boundary attaching
map. -/
theorem nativeBoundaryRootSourceIso_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeBoundaryRootSourceIso B n σ).hom ≫ nativeRootBoundaryChartMap B (n + 1) σ =
      nativeBoundaryChartMap B (n + 1) σ :=
  nativeBoundaryRootSourceMap_attachment B n σ

/-- The genuine entire source inverse retains exactly every unchanged original coface injection into the actual
all-face boundary. -/
theorem nativeBoundaryRootSourceIso_coface_inv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (i : Fin (n + 2)) :
    nativeRootBoundaryCofaceMap B n σ i ≫ (nativeBoundaryRootSourceIso B n σ).inv =
      nativeBoundaryCofaceChartMap B n σ i :=
  nativeRootBoundaryChartInverse_coface B n σ i

/-- The genuine entire source inverse retains exactly the whole unchanged original positive-chart inverse. -/
theorem nativeBoundaryRootSourceIso_positive_inv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativePositiveRootBoundaryMap B (n + 1) σ ≫ (nativeBoundaryRootSourceIso B n σ).inv =
      nativeBoundaryPositiveInverse B n σ :=
  nativeRootBoundaryChartInverse_positive B n σ

end SSet.Marked
