/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.LinearQuadraticRegulator
import Mathlib.Algebra.Order.Star.Real

open Matrix

namespace CSLibExt.MachineLearning.LinearQuadraticRegulator

-- One step from zero terminal cost: the Riccati update of `0` is `Q`.
example (A Q : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ)
    (R : Matrix (Fin 1) (Fin 1) ℝ) :
    riccatiMap A B Q R 0 = Q := by
  simp [riccatiMap]

-- The scalar integrator `x_{t+1} = x_t + u_t` with unit costs: every control sequence over three
-- steps costs at least the Riccati value, and the linear feedback attains it.
example (x₀ : Fin 1 → ℝ) (u : ℕ → Fin 1 → ℝ) :
    x₀ ⬝ᵥ (riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 3 *ᵥ x₀) ≤
      lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 x₀ u 3 :=
  lqrCost_ge PosSemidef.one PosDef.one PosSemidef.zero 3 x₀ u

example (x₀ : Fin 1 → ℝ) : ∃ u : ℕ → Fin 1 → ℝ,
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 x₀ u 3 =
      x₀ ⬝ᵥ (riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 3 *ᵥ x₀) :=
  (lqrCost_feedback PosSemidef.one PosDef.one PosSemidef.zero 3 x₀).imp fun _ h => h.1

-- In the scalar integrator, one step from x = 2 with terminal and input costs one
-- has cost 4 under zero control and minimum 2. The excess is exactly the residual cost.
example :
    let x : Fin 1 → ℝ := fun _ => 2
    let u : ℕ → Fin 1 → ℝ := fun _ => 0
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 1 x u 1 = 4 ∧
    x ⬝ᵥ (riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 0 1 1 1 *ᵥ x) = 2 := by
  let x : Fin 1 → ℝ := fun _ => 2
  let u : ℕ → Fin 1 → ℝ := fun _ => 0
  have hsum : (1 + 1 : Matrix (Fin 1) (Fin 1) ℝ) = (2 : ℝ) • 1 := by
    rw [two_smul]
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (2⁻¹ : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, Matrix.one_mul, ← smul_assoc, smul_eq_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  have h := lqrCost_eq_riccati_add_feedback_residual (A := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (B := 1) PosSemidef.zero PosDef.one PosSemidef.one 1 x u
  have hcost : lqrCost 1 1 0 1 1 x u 1 = 4 := by
    norm_num [lqrCost, lqrState, x, u, Finset.sum_range_one, Matrix.one_mulVec,
      dotProduct, Fin.sum_univ_one]
  change lqrCost 1 1 0 1 1 x u 1 = 4 ∧ _
  refine ⟨hcost, ?_⟩
  rw [hcost] at h
  simp only [Finset.sum_range_one] at h
  change 4 = x ⬝ᵥ (riccatiCostToGo 1 1 0 1 1 1 *ᵥ x) + _ at h
  simp only [Nat.sub_self, riccatiCostToGo, lqrState, riccatiGain,
    Matrix.transpose_one, Matrix.mul_one, hsum, hinv,
    Matrix.smul_mulVec, Matrix.one_mulVec, u, zero_add,
    Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_one, x] at h ⊢
  norm_num at h
  linarith

-- Changing the tail of a minimizing stream does not change its finite-horizon optimality.
example : ∃ u v : ℕ → Fin 1 → ℝ,
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 0 0 u 1 = 0 ∧
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 0 0 v 1 = 0 ∧
    u 0 = v 0 ∧ u 1 ≠ v 1 := by
  obtain ⟨u, hu, hmin⟩ := exists_lqrCost_minimizer_unique_prefix
    (σ := Fin 1) (ι := Fin 1) (A := 1) (B := 1)
    PosSemidef.zero PosDef.one PosSemidef.zero 1 0
  have hu0 : lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 0 0 u 1 = 0 := by simpa using hu
  let z : ℕ → Fin 1 → ℝ := fun _ _ => 0
  let v : ℕ → Fin 1 → ℝ := fun t _ => if t = 0 then 0 else 1
  have hz : lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 0 0 z 1 = 0 := by
    simp [lqrCost, z]
  have hv : lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 0 0 v 1 = 0 := by
    simp [lqrCost, v]
  have hz0 := (hmin z).2 (hz.trans hu0.symm) 0 (by decide)
  have hv0 := (hmin v).2 (hv.trans hu0.symm) 0 (by decide)
  refine ⟨z, v, hz, hv, hz0.trans hv0.symm, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [z, v] at hh

-- The two-step scalar integrator has distinct gains 1/3 and 1/2. With controls
-- (2, -2), its states are (6, 8, 6) and its cost decomposes as 44 = 12 + 24 + 8.
example :
    let x₀ : Fin 1 → ℝ := fun _ => 6
    let u : ℕ → Fin 1 → ℝ := fun t _ => if t = 0 then 2 else -2
    let M := riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 0 1 1
    let x := lqrState 1 1 x₀ u
    let term := fun t =>
      let j := 2 - 1 - t
      let e := u t + riccatiGain 1 1 1 (M j) *ᵥ x t
      e ⬝ᵥ ((1 + M j) *ᵥ e)
    term 0 = 24 ∧ term 1 = 8 ∧
      lqrCost 1 1 0 1 1 x₀ u 2 = x₀ ⬝ᵥ (M 2 *ᵥ x₀) + ((24 : ℝ) + 8) ∧
      lqrCost 1 1 0 1 1 x₀ u 2 = 44 ∧ x₀ ⬝ᵥ (M 2 *ᵥ x₀) = 12 := by
  intro x₀ u M x term
  have hinv (a : ℝ) (ha : a ≠ 0) :
      (a • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = a⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, Matrix.one_mul, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ ha, one_smul]
  have hS₀ : (1 + M 0) = (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    change (1 + 1 : Matrix (Fin 1) (Fin 1) ℝ) = _
    rw [two_smul]
  have hM₁ : M 1 = (1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    change riccatiMap 1 1 0 1 (M 0) = _
    have hM₀ : M 0 = 1 := rfl
    have hsum : (1 + 1 : Matrix (Fin 1) (Fin 1) ℝ) = (2 : ℝ) • 1 := by
      rw [two_smul]
    simp only [hM₀, riccatiMap, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul, zero_add]
    rw [hsum, hinv 2 (by norm_num)]
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    norm_num [Matrix.sub_apply, Matrix.smul_apply]
  have hS₁ : (1 + M 1) = (3 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hM₁]
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    norm_num [Matrix.add_apply, Matrix.smul_apply]
  have hterm₀ : term 0 = 24 := by
    change (u 0 + riccatiGain 1 1 1 (M 1) *ᵥ x 0) ⬝ᵥ
      ((1 + M 1) *ᵥ (u 0 + riccatiGain 1 1 1 (M 1) *ᵥ x 0)) = _
    unfold riccatiGain
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hS₁, hinv _ (by norm_num), hM₁, smul_mul_assoc, Matrix.one_mul, smul_smul]
    norm_num [x, x₀, u, lqrState, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_one]
  have hterm₁ : term 1 = 8 := by
    change (u 1 + riccatiGain 1 1 1 (M 0) *ᵥ x 1) ⬝ᵥ
      ((1 + M 0) *ᵥ (u 1 + riccatiGain 1 1 1 (M 0) *ᵥ x 1)) = _
    unfold riccatiGain
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hS₀, hinv _ (by norm_num), show M 0 = 1 from rfl, Matrix.mul_one]
    norm_num [x, x₀, u, lqrState, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_one]
  have he : lqrCost 1 1 0 1 1 x₀ u 2 = x₀ ⬝ᵥ (M 2 *ᵥ x₀) +
      ∑ t ∈ Finset.range 2, term t := by
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
      (lqrCost_eq_riccati_add_feedback_residual (σ := Fin 1) (ι := Fin 1) (A := 1) (B := 1)
        PosSemidef.zero PosDef.one PosSemidef.one 2 x₀ u)
  rw [Finset.sum_range_succ, Finset.sum_range_one, hterm₀, hterm₁] at he
  have hcost : lqrCost 1 1 0 1 1 x₀ u 2 = 44 := by
    norm_num [lqrCost, lqrState, x₀, u, Finset.sum_range_succ, Matrix.one_mulVec,
      Pi.add_apply, dotProduct, Fin.sum_univ_one]
  exact ⟨hterm₀, hterm₁, he, hcost, by linarith only [he, hcost]⟩

-- At horizon zero, arbitrary controls have no effect; only the nonzero terminal cost remains.
example (u : ℕ → Fin 1 → ℝ) :
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 0 1 1 (fun _ => 3) u 0 = 9 := by
  have h := lqrCost_eq_riccati_add_feedback_residual (σ := Fin 1) (ι := Fin 1) (A := 1)
    (B := 1) PosSemidef.zero PosDef.one PosSemidef.one 0 (fun _ => 3) u
  norm_num [riccatiCostToGo, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one] at h
  exact h

end CSLibExt.MachineLearning.LinearQuadraticRegulator
