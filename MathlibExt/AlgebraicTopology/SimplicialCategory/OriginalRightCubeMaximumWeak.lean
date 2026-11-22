/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeMaximumStages

/-!
# The SAME original quotient-cube maximum is weak on every input

The original boundary cell attachments prove comparison weakness
by induction on the genuine original dimension bound. The actual
whole skeleton colimit then proves weakness for every original
simplicial set. Every source, cell, cofan and terminal map is retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The SAME original full maximum is weak on every original input with a genuine finite dimension bound. -/
theorem maximum_weak_of_dimensionLT (n : ℕ) :
    ∀ (K : SSet.{u}), SSet.HasDimensionLT K n →
      SSet.realizationWeakEquivalences (maximum K) := by
  induction n with
  | zero =>
      intro K hK
      let _ : SSet.HasDimensionLT K 0 := hK
      have hInitial : IsInitial K :=
        (SSet.Subcomplex.isInitialBot (X := K)).ofIso (SSet.OriginalSkeletonDimension.emptyIso K)
      exact maximum_initial_weak K hInitial
  | succ n ih =>
      intro K hK
      let _ : SSet.HasDimensionLT K (n+1) := hK
      let c := SSet.relativeCellComplex K
      let a := c.attachCells n (not_isMax n)
      have hA : SSet.realizationWeakEquivalences (maximum a.cofan₁.pt) :=
        maximum_weak_of_cofan (fun _ : a.ι => (∂Δ[n] : SSet.{u})) a.cofan₁ a.isColimit₁
          (fun _ => ih (∂Δ[n] : SSet.{u}) inferInstance)
      have hB : SSet.realizationWeakEquivalences (maximum a.cofan₂.pt) :=
        maximum_weak_of_cofan (fun _ : a.ι => (Δ[n] : SSet.{u})) a.cofan₂ a.isColimit₂
          (fun _ => maximum_simplex_weak ⦋n⦌)
      have hStage : SSet.realizationWeakEquivalences (maximum (c.F.obj n)) :=
        ih (c.F.obj n) (boundaryStage_dimension K n)
      let _ : Mono a.m := boundaryAttachment_mono K n
      have hNext : SSet.realizationWeakEquivalences (maximum (c.F.obj (n+1))) :=
        maximum_weak_of_isPushout a.isPushout.flip hA hB hStage
      exact maximum_weak_of_iso (boundaryStageIso K (n+1)) hNext

/-- The SAME actual original full quotient-cube maximum is a realization weak equivalence for EVERY original simplicial
set. -/
theorem maximum_weak (K : SSet.{u}) :
    SSet.realizationWeakEquivalences (maximum K) := by
  let c := SSet.relativeCellComplex K
  exact maximum_weak_of_filtered_cocone c.F ⟨K,c.incl⟩ c.isColimit
    (fun n => maximum_weak_of_dimensionLT n (c.F.obj n) (boundaryStage_dimension K n))

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
