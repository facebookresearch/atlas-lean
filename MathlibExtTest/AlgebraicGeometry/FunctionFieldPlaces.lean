/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.FunctionFieldPlaces

namespace FunctionFieldPlacesTest

open MathlibExt.AlgebraicGeometry.FaltingsWanted.AlgebraicGeometry.Faltings
open scoped WithZero

private noncomputable instance ratFuncBundledFunctionField (K : Type*) [Field K] :
    BundledFunctionField K (RatFunc K) where
  toAlgebra := Algebra.id _
  toIsScalarTower := inferInstance
  toFinite := inferInstance

section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

private theorem not_mem_inftyValuationSubring :
    (RatFunc.X : RatFunc K) ∉ (RatFunc.inftyValuation K).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X]
  simp

private noncomputable def infinityAlgebra : Subalgebra K (RatFunc K) :=
  { (RatFunc.inftyValuation K).valuationSubring.toSubring.toSubsemiring with
    algebraMap_mem' := fun c ↦ (Valuation.mem_valuationSubring_iff _ _).mpr
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one (RatFunc.inftyValuation K) c) }

private noncomputable def infinityPlace : Place K (RatFunc K) where
  toSubalgebra := infinityAlgebra K
  neg_mem' := (RatFunc.inftyValuation K).valuationSubring.neg_mem _
  mem_or_inv_mem' := (RatFunc.inftyValuation K).valuationSubring.mem_or_inv_mem
  ne_top := by
    intro h
    have hX : (RatFunc.X : RatFunc K) ∈ infinityAlgebra K := by rw [h]; trivial
    exact not_mem_inftyValuationSubring K hX

example :
    {v : Place K (RatFunc K) | (RatFunc.X : RatFunc K) ∉ v}.Finite ∧
      {v : Place K (RatFunc K) | (RatFunc.X : RatFunc K) ∉ v}.Nonempty :=
  ⟨finite_setOf_place_notMem K _, ⟨infinityPlace K, not_mem_inftyValuationSubring K⟩⟩

-- The diagonal map also sends elements with poles to adeles, without modifying their coordinates.
example : Adele.principal K (RatFunc.X : RatFunc K) (infinityPlace K) = RatFunc.X :=
  Adele.principal_apply K _ _

end

example (K : Type*) [Field K] (c : K) :
    {v : Place K (RatFunc K) | algebraMap K (RatFunc K) c ∉ v} = ∅ := by
  exact Set.eq_empty_iff_forall_notMem.mpr fun v h ↦ h (v.algebraMap_mem c)

end FunctionFieldPlacesTest
