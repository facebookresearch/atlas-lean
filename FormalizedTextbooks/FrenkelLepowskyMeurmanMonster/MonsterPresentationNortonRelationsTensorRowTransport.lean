/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorColumnTransport

/-! Whole tensor transport from arbitrary source rows to arbitrary output columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- Full local tensor transport follows from complete spatial rows and complete spin columns. -/
theorem monsterNortonLocal_tensor_rows_actual {I K : Type*} [Fintype I] [Fintype K]
    (f : localFiberSubgroup) (s : I → SpinSpace) (b : I → Fin 24 → ℝ)
    (c : K → Fin 24) (w : K → I → ℝ) (t : K → SpinSpace)
    (hb : ∀ i, f.val.2.val (b i) =
      ∑ k, w k i • (Pi.single (c k) 1 : Fin 24 → ℝ))
    (hs : ∀ k, f.val.1.val (∑ i, w k i • s i) = t k) :
    localGriessRepresentation f
      (∑ i, monsterNortonTensorLift (conwayTensorCoordinates (s i ⊗ₜ[ℝ] b i))) =
        ∑ k, monsterNortonTensorLift (conwayTensorCoordinates
          (t k ⊗ₜ[ℝ] (Pi.single (c k) 1 : Fin 24 → ℝ))) := by
  rw [map_sum]
  simp_rw [monsterNortonLocal_tensor_product_actual, hb]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul]
  rw [Finset.sum_comm]
  have hspin (k : K) : (∑ i, w k i • f.val.1.val (s i)) = t k := by
    have h := hs k
    simpa only [map_sum, map_smul] using h
  have hcolumn (k : K) :
      (∑ i, w k i • monsterNortonTensorLift (conwayTensorCoordinates
        (f.val.1.val (s i) ⊗ₜ[ℝ] (Pi.single (c k) 1 : Fin 24 → ℝ)))) =
        monsterNortonTensorLift (conwayTensorCoordinates
          (t k ⊗ₜ[ℝ] (Pi.single (c k) 1 : Fin 24 → ℝ))) := by
    have h := congrArg (fun v : SpinSpace => monsterNortonTensorLift
      (conwayTensorCoordinates (v ⊗ₜ[ℝ] (Pi.single (c k) 1 : Fin 24 → ℝ)))) (hspin k)
    simpa only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul] using h
  simp_rw [hcolumn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
