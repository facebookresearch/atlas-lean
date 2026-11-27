/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation

/-!
# Realization coordinates under subcomplex inclusion

A nondegenerate simplex of a subcomplex maps to a nondegenerate simplex of
the ambient simplicial set with the same dimension. At the same standard-simplex
coordinate, its realization presentation maps to the presentation of the image
carrier under the realized subcomplex inclusion.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/--
The nondegenerate carrier in the ambient simplicial set obtained by applying
the subcomplex inclusion to a nondegenerate simplex.
-/
def mapCarrier (s : (A : SSet.{u}).N) : X.N :=
  SSet.N.mk
    (SSet.nonDegenerateEmbeddingOfMono A.ι s.dim ⟨s.simplex, s.nonDegenerate⟩).val
    (SSet.nonDegenerateEmbeddingOfMono A.ι s.dim ⟨s.simplex, s.nonDegenerate⟩).property

/--
At the same barycentric coordinate, evaluating the ambient image carrier equals
the realized subcomplex inclusion applied to the original presentation.
-/
theorem sigmaToTop_mapCarrier (s : (A : SSet.{u}).N)
    (x : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    SSet.sigmaToTop X ⟨mapCarrier A s, x⟩ =
      SSet.toTop.map A.ι (SSet.sigmaToTop (A : SSet.{u}) ⟨s, x⟩) := by
  have hEq : (mapCarrier A s).simplex = A.ι.app _ s.simplex := rfl
  have hY : SSet.yonedaEquiv.symm ((mapCarrier A s).simplex) =
      SSet.yonedaEquiv.symm s.simplex ≫ A.ι := by
    rw [hEq]
    exact (SSet.yonedaEquiv_symm_comp s.simplex A.ι).symm
  have hMap : SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex ≫ A.ι) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) ≫ SSet.toTop.map A.ι :=
    SSet.toTop.map_comp _ _
  -- The mapped carrier has definitionally the same dimension as `s`, so both
  -- sides use the same homeomorphism; state the unfolded goal with `s.dim`.
  change SSet.toTop.map (SSet.yonedaEquiv.symm ((mapCarrier A s).simplex))
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x) =
      SSet.toTop.map A.ι (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x))
  have h1 : SSet.toTop.map (SSet.yonedaEquiv.symm ((mapCarrier A s).simplex))
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex ≫ A.ι)
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x) :=
    congrArg (fun m => SSet.toTop.map m
      ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x)) hY
  have h2 : SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex ≫ A.ι)
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x) =
      SSet.toTop.map A.ι (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
        ((SimplexCategory.toTopHomeo ⦋s.dim⦌).symm x)) := by
    rw [hMap]
    rfl
  exact h1.trans h2

end Subcomplex

end SSet
