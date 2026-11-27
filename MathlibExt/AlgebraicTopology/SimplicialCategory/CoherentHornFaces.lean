/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Actual original vertices and coherent faces of a supplied horn map

The data below is extracted from the actual map into the existing
coherent nerve. Original vertices are individual objects and each supplied
face is a genuine enriched functor. All two-face compatibility equations
are proved from the original horn map; none is a comparison certificate.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornFaces
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The supplied original horn vertex read as its individual enriched object. -/
def object (t : Fin (n + 3)) : C :=
  vertexOf C (f.app (op ⦋0⦌) ⟨SSet.stdSimplex.obj₀Equiv.symm t, by simp⟩)

/-- The actual original coherent face functor obtained from the supplied horn map. -/
def faceFunctor (j : Fin (n + 3)) (hj : j ≠ i) : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C :=
  f.app (op ⦋n + 1⦌) (SSet.horn.face i j hj)

/-- Each supplied actual face retains the same original horn vertex under its genuine
ordinal face map. -/
theorem faceFunctor_obj (j : Fin (n + 3)) (hj : j ≠ i) (t : coherentSimplex.{u} ⦋n + 1⦌) :
    (faceFunctor f j hj).obj t = object f (j.succAbove t.as.down) := by
  have h := congr($(f.naturality (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ t.as.down).op)
    (SSet.horn.face i j hj))
  exact (congrArg (vertexOf C) h).symm

/-- The supplied coherent face is exactly the original simplex classified by its actual face map. -/
theorem faceFunctor_yoneda (j : Fin (n + 3)) (hj : j ≠ i) :
    faceFunctor f j hj = SSet.yonedaEquiv (SSet.horn.ι i j hj ≫ f) := rfl

/-- Every supplied pair of original coherent faces agrees on the whole common coherent subface. -/
theorem faceFunctor_compatibility (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :
    coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫ faceFunctor f j hj =
      coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
        faceFunctor f k hk := by
  have h := (SSet.horn.IsCompatible.of_hom f).δ_pred_comp j k hj hk hjk
  have he := congrArg (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋n⦌)) h
  have hl := SSet.yonedaEquiv_naturality
    (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) (SSet.horn.ι i j hj ≫ f)
  have hr := SSet.yonedaEquiv_naturality
    (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) (SSet.horn.ι i k hk ≫ f)
  exact hl.trans (he.trans hr.symm)

end CategoryTheory.CoherentRealization.HornFaces
