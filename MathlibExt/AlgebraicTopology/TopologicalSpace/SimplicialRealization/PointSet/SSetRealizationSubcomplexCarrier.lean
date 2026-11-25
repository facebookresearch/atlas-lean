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
# Naturality of nondegenerate carriers along subcomplex inclusions

For `A : X.Subcomplex`, map a nondegenerate carrier `s : (A : SSet).N` along
the mono `A.ι` using the existing nondegenerate embedding, and show that
`SSet.sigmaToTop X` of the mapped carrier at the same standard-simplex
coordinate equals `SSet.toTop.map A.ι` applied to `SSet.sigmaToTop A` of the
original presentation.

API-reuse map (all `reuse`; no `local` entry):
* mapped carrier: `SSet.nonDegenerateEmbeddingOfMono`
  (`MathlibExt/AlgebraicTopology/SimplicialSet/NondegenerateEmbedding.lean`);
* classifier identification: `SSet.yonedaEquiv_symm_comp`
  (`Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`);
* same-coordinate realization point: `SSet.sigmaToTop`
  (`RealizationPresentation`), which already bundles `SSet.yonedaEquiv.symm`
  with `SimplexCategory.toTopHomeo.symm`; the mapped carrier has definitionally
  the same dimension as the original, so the homeomorphism needs no transport
  (`SimplexCategory.toTopHomeo_naturality_apply` is the designated tool when
  dimensions genuinely differ);
* map fusion: `SSet.toTop.map_comp` with `CategoryTheory.comp_apply`.

Nonclaims: no new quotient relation, no carrier uniqueness theorem, no
compact-support theorem, no fibration or model-category result.
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
