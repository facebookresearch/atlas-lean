/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentStandardEvaluation

/-!
# The same standard-simplex inverse and full insertion

The adjunction-derived standard simplex Iso has the 
simplex insertion as its inverse. Every input
simplex is inserted by the same realized Yoneda map, with both 
functor directions retained and no global QE outcome assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- The same native top simplex of the full standard simplex. -/
def topSimplex (n : SimplexCategory) : (SSet.stdSimplex.{u}.obj n).obj (op n) :=
  SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.{u}.obj n))

/-- The inverse of the same standard simplex Iso is its simplex insertion. -/
theorem simplexIso_inverse_insertion (n : SimplexCategory) :
    (simplexIso.{u} n).inv = simplexInto (SSet.stdSimplex.{u}.obj n) (topSimplex n) := by
  have h := congrArg
    (fun f : SSet.stdSimplex.{u}.obj n ⟶ coherentNerveFunctor.obj (coherentSimplex.{u} n) =>
      f.app (op n) (topSimplex n)) (simplexIso_hom_adjunction.{u} n)
  change simplexInto (SSet.stdSimplex.{u}.obj n) (topSimplex n) ≫ (simplexIso.{u} n).hom =
    (standardChart n).app (op n) (topSimplex n) at h
  have ht : (standardChart.{u} n).app (op n) (topSimplex n) = 𝟙 (coherentSimplex.{u} n) :=
    SSet.yonedaEquiv_symm_app_id _
  apply (cancel_mono (simplexIso.{u} n).hom).1
  exact (simplexIso.{u} n).inv_hom_id.trans (h.trans ht).symm

/-- EVERY input simplex has its same realized Yoneda
insertion formula. -/
theorem simplexIso_hom_insertion {K : SSet.{u}} {n : SimplexCategory} (σ : K.obj (op n)) :
    (simplexIso.{u} n).hom ≫ simplexInto K σ = realizationMap (SSet.yonedaEquiv.symm σ) := by
  have h := unit_simplex_naturality (SSet.yonedaEquiv.symm σ) (topSimplex.{u} n)
  change simplexInto (SSet.stdSimplex.{u}.obj n) (topSimplex n) ≫
    realizationMap (SSet.yonedaEquiv.symm σ) =
    simplexInto K ((SSet.yonedaEquiv.symm σ).app (op n) (topSimplex n)) at h
  have ht : (SSet.yonedaEquiv.symm σ).app (op n) (topSimplex n) = σ :=
    SSet.yonedaEquiv_symm_app_id σ
  have hi : (simplexIso.{u} n).inv ≫ realizationMap (SSet.yonedaEquiv.symm σ) = simplexInto K σ :=
    (congrArg (fun F => F ≫ realizationMap (SSet.yonedaEquiv.symm σ))
      (simplexIso_inverse_insertion.{u} n)).trans (h.trans (congrArg (simplexInto K) ht))
  exact (congrArg (fun F => (simplexIso.{u} n).hom ≫ F) hi).symm.trans (Iso.hom_inv_id_assoc _ _)

end CategoryTheory.CoherentRealization
