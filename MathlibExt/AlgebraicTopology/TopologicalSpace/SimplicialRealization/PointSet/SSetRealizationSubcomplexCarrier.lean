/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation

/-!
# Realization presentations under subcomplex inclusions

The map `SSet.Subcomplex.mapCarrier A` sends nondegenerate simplices of a
subcomplex `A` to ambient nondegenerate simplices through
`SSet.nonDegenerateEmbeddingOfMono`, preserving their dimension. The theorem
`sigmaToTop_mapCarrier` states that realization of the mapped carrier at a
given standard-simplex point agrees with applying the realization of `A.ι`
to the original presentation.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- Map a nondegenerate carrier of the subcomplex along the inclusion mono. -/
def mapCarrier (s : (A : SSet.{u}).N) : X.N :=
  SSet.N.mk
    (SSet.nonDegenerateEmbeddingOfMono A.ι s.dim ⟨s.simplex, s.nonDegenerate⟩).val
    (SSet.nonDegenerateEmbeddingOfMono A.ι s.dim ⟨s.simplex, s.nonDegenerate⟩).property

/-- Carrier coherence of `SSet.sigmaToTop` along a subcomplex inclusion. -/
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
  -- The carrier map preserves dimension, so both presentations use the
  -- same standard-simplex coordinate.
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
