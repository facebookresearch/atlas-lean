/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeMaximumColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSkeletonDimension

/-!
# Exact original cutoff stages for the quotient-cube maximum

The original native simplicial boundary cell complex has the SAME
original skeleton stages, dimensional bounds and complete cutoff
isomorphism. Its original cells, cofans and terminal map are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- A genuine original source isomorphism transports the SAME full original maximum weak component. -/
theorem maximum_weak_of_iso {K L : SSet.{u}} (e : K ≅ L)
    (hK : SSet.realizationWeakEquivalences (maximum K)) :
    SSet.realizationWeakEquivalences (maximum L) := by
  let W := SSet.realizationWeakEquivalences.{u}
  have h := W.comp_mem (maximum K) e.hom hK (W.of_isIso e.hom)
  have h' : W (map e.hom ≫ maximum L) := (maximum_naturality e.hom).symm ▸ h
  let _ : IsIso (map e.hom) := functor.map_isIso e.hom
  exact W.of_precomp (map e.hom) (maximum L) (W.of_isIso _) h'

/-- The SAME complete original maximum at a genuine original initial object is an isomorphism and hence weak. -/
theorem maximum_initial_weak (K : SSet.{u}) (hK : IsInitial K) :
    SSet.realizationWeakEquivalences (maximum K) := by
  let hQ : IsInitial (object K) := hK.isInitialObj functor K
  let e := hQ.uniqueUpToIso hK
  have h : maximum K = e.hom := hQ.hom_ext _ _
  exact h.symm ▸ SSet.realizationWeakEquivalences.of_isIso e.hom

/-- The SAME native original boundary-cell stage is exactly the original simplicial cutoff skeleton. -/
theorem boundaryStage_eq_skeleton (K : SSet.{u}) (n : ℕ) :
    (SSet.relativeCellComplex K).F.obj n = (K.skeleton n : SSet.{u}) := by
  change ((SSet.Subcomplex.range (⊥ : K.Subcomplex).ι ⊔ K.skeleton n : K.Subcomplex) : SSet.{u}) = _
  have hRange : SSet.Subcomplex.range (⊥ : K.Subcomplex).ι = ⊥ := by
    ext q x
    simp
  rw [hRange]
  congr 1
  exact le_antisymm (sup_le bot_le le_rfl) le_sup_right

/-- Every SAME original native stage has its genuine original cutoff dimension. -/
theorem boundaryStage_dimension (K : SSet.{u}) (n : ℕ) :
    SSet.HasDimensionLT ((SSet.relativeCellComplex K).F.obj n) n :=
  (boundaryStage_eq_skeleton K n).symm ▸ SSet.OriginalSkeletonDimension.hasDimensionLT K n

/-- At an actual original dimension bound, the SAME entire native cutoff stage is the whole original input. -/
def boundaryStageIso (K : SSet.{u}) (n : ℕ) [SSet.HasDimensionLT K n] :
    (SSet.relativeCellComplex K).F.obj n ≅ K :=
  eqToIso (boundaryStage_eq_skeleton K n) ≪≫ SSet.OriginalSkeletonDimension.inclusionIso K n

/-- Every original boundary-cell cofan map is genuinely monic, retaining the full supplied original cofans. -/
theorem boundaryAttachment_mono (K : SSet.{u}) (n : ℕ) :
    Mono ((SSet.relativeCellComplex K).attachCells n (not_isMax n)).m := by
  let c := (SSet.relativeCellComplex K).attachCells n (not_isMax n)
  let F : Discrete c.ι ⥤ SSet.{u} := Discrete.functor (fun _ => (∂Δ[n] : SSet.{u}))
  let G : Discrete c.ι ⥤ SSet.{u} := Discrete.functor (fun _ => (Δ[n] : SSet.{u}))
  let α : F ⟶ G := Discrete.natTrans (fun _ => (SSet.boundary.{u} n).ι)
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms SSet.{u}) F G c.cofan₁ c.cofan₂
    c.isColimit₁ c.isColimit₂ α (fun _ => by
      change Mono (SSet.boundary.{u} n).ι
      infer_instance) c.m (fun i => c.hm i.as)

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
