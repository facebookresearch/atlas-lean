/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaces
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Every whole original coherent boundary face

The supplied actual boundary map has all its original vertices and
complete enriched face functors. Every common-face equation follows
from its original naturality. Restriction to any original horn
retains the same whole faces and individual vertices.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryFaces
open SimplicialEnrichment

variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n + 2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The supplied whole original boundary face functor at its same individual ordinal label. -/
def faceFunctor (j : Fin (n + 3)) : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C :=
  SSet.yonedaEquiv (SSet.boundary.ι j ≫ f)

/-- The SAME full original boundary contains each original horn. -/
theorem horn_le_boundary (i : Fin (n + 3)) :
    (Λ[n + 2, i] : (Δ[n + 2] : SSet.{u}).Subcomplex) ≤ ∂Δ[n + 2] := by
  rw [SSet.horn_eq_iSup]
  exact iSup_le (fun j => SSet.face_singleton_compl_le_boundary j.1)

/-- The actual original boundary map restricted to the same specified original horn. -/
def horn (i : Fin (n + 3)) : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
  SSet.Subcomplex.homOfLE (horn_le_boundary i) ≫ f

/-- The original horn restriction retains the same entire original supplied face. -/
theorem horn_face (i j : Fin (n + 3)) (hj : j ≠ i) :
    HornFaces.faceFunctor (horn f i) j hj = faceFunctor f j := by
  rw [HornFaces.faceFunctor_yoneda]
  congr 1

/-- Every pair of full original boundary faces agrees on the same whole original common face. -/
theorem faceFunctor_compatibility (j k : Fin (n + 3)) (hjk : j < k) :
    coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫ faceFunctor f j =
      coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
        faceFunctor f k := by
  have hδ :
      SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SSet.boundary.ι j =
        SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SSet.boundary.ι k := by
    apply (cancel_mono (SSet.boundary.{u} (n + 2)).ι).mp
    rw [Category.assoc, SSet.boundary.ι_ι, Category.assoc, SSet.boundary.ι_ι]
    have hd : SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SimplexCategory.δ k =
        SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SimplexCategory.δ j :=
      SimplexCategory.δ_comp_δ' (by simpa only [Fin.castSucc_castPred] using hjk)
    exact ((SSet.stdSimplex.{u}.map_comp _ _).symm.trans
      ((congrArg SSet.stdSimplex.{u}.map hd).trans (SSet.stdSimplex.{u}.map_comp _ _))).symm
  have h := congrArg (fun t => SSet.yonedaEquiv (t ≫ f)) hδ
  exact (SSet.yonedaEquiv_naturality
    (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) (SSet.boundary.ι j ≫ f)).trans
      (h.trans (SSet.yonedaEquiv_naturality
        (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) (SSet.boundary.ι k ≫ f)).symm)

end CategoryTheory.CoherentRealization.BoundaryFaces
