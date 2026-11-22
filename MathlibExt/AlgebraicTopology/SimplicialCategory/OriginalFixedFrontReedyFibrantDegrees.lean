/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyWeakAugmentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedZeroIso
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyComponentCofibrations
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantUnderObjects

/-!
# Genuine original fibrancy of every actual Reedy replacement degree

The actual opposite Reedy left factor is a cofibration. The genuine
cofree-matching component theorem proves its same degree cofibration;
unop is therefore a fibration in the original pointed Joyal model.
Its full original target is the zero quotient walking arrow, which is
fibrant. Every actual full generated degree is consequently fibrant.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits HomotopicalAlgebra
open scoped Simplicial CategoryTheory.SimplicialObject.reedyModelCategory

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The full original zero quotient is genuinely quasicategorical through its actual original walking-arrow
isomorphism. -/
theorem zeroObject_quasicategory : SSet.Quasicategory (FixedFrontCollapse.object.{u} 0) := by
  let _ : IsFibrant (JoyalSSet.ofSSet.obj (Δ[1] : SSet.{u})) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr
      (show SSet.Quasicategory (Δ[1] : SSet.{u}) from inferInstance)
  let _ : Fibration (JoyalSSet.ofSSet.map zeroObjectIso.{u}.hom) := by infer_instance
  have h := isFibrant_of_fibration (JoyalSSet.ofSSet.map zeroObjectIso.{u}.hom)
  exact (JoyalSSet.isFibrant_iff_quasicategory _).mp h

/-- The same original pointed zero quotient is genuinely fibrant in the actual named Under Joyal model. -/
theorem pointedZero_isFibrant : IsFibrant (pointedCopyFunctor.obj (pointedObject.{u} 0)) :=
  (isFibrant_under_iff _ _).mpr ((JoyalSSet.isFibrant_iff_quasicategory _).mpr zeroObject_quasicategory)

/-- Every actual original generated projection component is genuinely a fibration in the original pointed Joyal
model. -/
theorem reedyReplacementProjection_app_fibration (n : SimplexCategory) :
    Fibration (reedyReplacementProjection.{u}.app n) := by
  have hi := reversedFactorization.{u}.hi
  change SimplicialObject.reedyLeft (cofibrations PointedJoyal.{u}ᵒᵖ) reversedFactorization.i at hi
  have hc := SimplicialObject.component_cofibration_of_reedyLeft reversedFactorization.i hi n.len
  let _ : Cofibration (reversedFactorization.i.app (op ⦋n.len⦌)) := (cofibration_iff _).mpr hc
  have h : Fibration (reversedFactorization.i.app (op ⦋n.len⦌)).unop := inferInstance
  have hn : ⦋n.len⦌ = n := SimplexCategory.mk_len n
  cases hn
  exact h

/-- Every same full original Reedy replacement degree is genuinely fibrant in the actual original pointed Joyal
model. -/
theorem reedyReplacement_obj_isFibrant (n : SimplexCategory) : IsFibrant (reedyReplacement.{u}.obj n) := by
  let _ : IsFibrant (((Functor.const SimplexCategory).obj
      (pointedCopyFunctor.obj (pointedObject.{u} 0))).obj n) := by
    change IsFibrant (pointedCopyFunctor.obj (pointedObject.{u} 0))
    exact pointedZero_isFibrant
  let _ : Fibration (reedyReplacementProjection.{u}.app n) := reedyReplacementProjection_app_fibration n
  exact isFibrant_of_fibration (reedyReplacementProjection.app n)

/-- Every entire original generated Reedy carrier is consequently an actual quasicategory, with its full original
endpoints. -/
theorem reedyReplacement_raw_quasicategory (n : SimplexCategory) :
    SSet.Quasicategory (reedyReplacement.{u}.obj n).right.toSSet :=
  (JoyalSSet.isFibrant_iff_quasicategory _).mp
    ((isFibrant_under_iff _ _).mp (reedyReplacement_obj_isFibrant n))

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
