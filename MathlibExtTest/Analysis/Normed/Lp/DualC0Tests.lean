/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.DualC0

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Lp.DualC0

open scoped ENNReal Topology ZeroAtInfty

open MathlibExt.Analysis.Normed.Lp.DualC0

-- The norm of a basis vector of `c₀(ℕ, ℝ)` is the norm of its entry.
example : ‖c0Single (𝕜 := ℝ) (ι := ℕ) 0 (3 : ℝ)‖ = 3 := by
  rw [c0Single_norm, Real.norm_eq_abs]
  norm_num

-- The coordinates of a basis vector of `c₀(ℕ, ℝ)` vanish off the diagonal.
example : ((c0Single (𝕜 := ℝ) (ι := ℕ) 0 (2 : ℝ) : c0 ℝ ℕ) : ℕ → ℝ) 1 = 0 := by
  simp [c0Single_apply]

-- The pairing on `c₀(ℕ, ℝ)` picks out the product of the coordinates at `0`.
example : c0DualPairing (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ))
    (c0Single 0 (1 : ℝ)) = 3 := by
  rw [c0DualPairing_apply, tsum_eq_single 0]
  · simp [c0Single_apply]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

-- The pairing vanishes when the coordinates are supported at different indices.
example : c0DualPairing (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ))
    (c0Single 1 (1 : ℝ)) = 0 := by
  rw [c0DualPairing_apply, tsum_eq_single 0]
  · simp [c0Single_apply]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

-- The pairing is norm-preserving on a concrete `ℓ¹` vector.
example : ‖c0DualPairing (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ))‖ = 3 := by
  rw [c0DualPairing_norm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  rw [Real.norm_eq_abs]
  norm_num

-- The equiv is an isometry on a concrete `ℓ¹` vector.
example : ‖c0DualEquiv (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ))‖ = 3 := by
  rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  rw [Real.norm_eq_abs]
  norm_num

-- The equiv applies as the pairing.
example : c0DualEquiv (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ))
    = c0DualPairing (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (3 : ℝ)) :=
  rfl

-- Evaluation at `0` is pairing with the `0`-th basis vector.
example : c0DualPairing (𝕜 := ℝ) (ι := ℕ) (lp.single 1 0 (1 : ℝ))
    = c0Eval (𝕜 := ℝ) (ι := ℕ) 0 :=
  c0DualPairing_single_eq_eval 0

/-- The sequence `n ↦ 1 / (n + 1)`, as an element of `c₀(ℕ, ℝ)`. -/
noncomputable def testSeq : c0 ℝ ℕ :=
  c0OfLp ⟨fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1), memℓp_infty ⟨1, by
      rintro y ⟨n, rfl⟩
      show ‖(1 : ℝ) / ((n : ℝ) + 1)‖ ≤ 1
      rw [norm_div, norm_one, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      apply div_le_one_of_le₀
      · have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      · positivity⟩⟩ (by
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.cofinite (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    exact h)

-- Evaluation at `0` picks out the first term of `testSeq`.
example : c0Eval (𝕜 := ℝ) (ι := ℕ) 0 testSeq = 1 := by
  show ((testSeq : c0 ℝ ℕ) : ℕ → ℝ) 0 = 1
  simp [testSeq]

-- Evaluation at `1` picks out the second term of `testSeq`.
example : c0Eval (𝕜 := ℝ) (ι := ℕ) 1 testSeq = 1 / 2 := by
  show ((testSeq : c0 ℝ ℕ) : ℕ → ℝ) 1 = 1 / 2
  simp [testSeq]
  norm_num

/-- The public canonical space has its standard completeness instance for any index. -/
example (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) : CompleteSpace (c0 𝕜 ι) := inferInstance

-- These direct standard-type checks exercise both an inhabited and an empty index.
#check (c0DualEquiv (𝕜 := ℝ) (ι := ℕ) :
  lp (fun _ : ℕ => ℝ) 1 ≃ₗᵢ[ℝ] StrongDual ℝ C₀(ℕ, ℝ))
#check (c0DualEquiv (𝕜 := ℂ) (ι := Empty) :
  lp (fun _ : Empty => ℂ) 1 ≃ₗᵢ[ℂ] StrongDual ℂ C₀(Empty, ℂ))

/-- The compatibility representation preserves the nonconstant sequence coordinate. -/
example : (c0LpEquiv (𝕜 := ℝ) (ι := ℕ) testSeq : lp (fun _ : ℕ => ℝ) ∞) 1 = 1 / 2 := by
  change (testSeq : ℕ → ℝ) 1 = 1 / 2
  simp [testSeq]
  norm_num

/-- The complex pairing is bilinear multiplication, without conjugating a coefficient. -/
example : c0DualPairing (𝕜 := ℂ) (ι := ℕ) (lp.single 1 0 Complex.I)
    (c0Single 0 Complex.I) = -1 := by
  rw [c0DualPairing_apply, tsum_eq_single 0]
  · simp [c0Single_apply]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

end MathlibExtTest.Analysis.Normed.Lp.DualC0
