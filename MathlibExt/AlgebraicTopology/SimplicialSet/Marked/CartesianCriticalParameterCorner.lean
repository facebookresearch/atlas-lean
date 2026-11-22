/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalProductPairing
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ComapArrowIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-!
# The original critical parameter corner is its native marked product union

The original source marking covers all target marks. The actual native
scalar pushout and product symmetry compare its entire corner with the
critical-horn product union, carrying the inherited original marks.
This transfers the native controlled pairing filler without changing
any parameter, edge, cell or base simplex.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The complete original cartesian parameter corner is the same inherited marked critical-horn product union. -/
def cartesianCriticalParameterUnionIso (m n : ℕ) :
    Arrow.mk (parameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalCell.{u} m)) ≅
      Arrow.mk (comapHom
        (prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u})))
        (Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)).ι) := by
  let f := parameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalCell.{u} m)
  let _ : Mono (cartesianCriticalCell.{u} m) := cartesianCriticalCell_mono m
  let _ : Mono f := parameterPushoutProduct_mono _ _
  let s := parameterUnderlyingPushoutIso (boundary.{u} n).ι (cartesianCriticalCell.{u} m)
  let e := s ≪≫ MonoidalCategory.Arrow.PushoutProduct.braiding
    (Arrow.mk (boundary.{u} n).ι) (Arrow.mk (horn.{u} (m + 2) (Fin.last (m + 2))).ι) ≪≫
    (Subcomplex.unionProd.ιIso (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)).symm
  let t := prodSwapIso (max (Δ[n] : SSet.{u})) (cartesianCriticalTarget.{u} m)
  have ht : e.hom.right = t.hom.hom := by
    change 𝟙 _ ≫ (β_ (Δ[n] : SSet.{u}) (Δ[m + 2] : SSet.{u})).hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  exact comapArrowIso f
    (parameterPushoutProduct_markingSurjective _ _ (cartesianCriticalCell_markingSurjective m))
    _ (Arrow.leftFunc.mapIso e) t (e.hom.w.trans (congrArg (fun z => f.hom ≫ z) ht))

/-- Every whole original scalar boundary/critical-cell square lifts against the supplied native cartesian projection. -/
theorem cartesianCriticalParameter_boundary_lifting (m n : ℕ) {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty (parameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalCell.{u} m))
      (cartesianProjection p) :=
  (HasLiftingProperty.iff_of_arrow_iso_left (cartesianCriticalParameterUnionIso m n) (cartesianProjection p)).mpr
    (cartesianCriticalProduct_lifting m n p)

end SSet.Marked
