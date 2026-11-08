/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.Dual

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Lp.Dual

open scoped ENNReal

open MathlibExt.Analysis.Normed.Lp.Dual

instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
instance : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_refl _⟩
instance : Fact ((1 : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞)) := ⟨le_top⟩

-- The pairing on `ℓ²(ℕ, ℝ)` picks out the product of the coordinates at `0`.
example : (lpDualPairing (𝕜 := ℝ) (ι := ℕ) (p := 2) (q := 2))
    (lp.single 2 0 (3 : ℝ)) (lp.single 2 0 (1 : ℝ)) = 3 := by
  rw [lpDualPairing_apply]
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

-- The pairing is norm-preserving on a concrete `ℓ²` vector.
example : ‖lpDualPairing (𝕜 := ℝ) (ι := ℕ) (p := 2) (q := 2)
    (lp.single 2 0 (3 : ℝ))‖ = 3 := by
  rw [lpDualPairing_norm (by simp : (2 : ℝ≥0∞) ≠ ⊤),
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  rw [Real.norm_eq_abs]
  norm_num

-- The equiv is an isometry on a concrete `ℓ²` vector.
example : ‖lpDualEquiv (𝕜 := ℝ) (ι := ℕ) (p := 2) (q := 2) (by simp)
    (lp.single 2 0 (3 : ℝ))‖ = 3 := by
  rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  rw [Real.norm_eq_abs]
  norm_num

-- The equiv applies as the pairing.
example : (lpDualEquiv (𝕜 := ℝ) (ι := ℕ) (p := 2) (q := 2) (by simp))
    (lp.single 2 0 (3 : ℝ)) = lpDualPairing (𝕜 := ℝ) (ι := ℕ) (p := 2) (q := 2)
    (lp.single 2 0 (3 : ℝ)) :=
  rfl

-- The `p = 1`, `q = ⊤` case: pairing a functional from `ℓ^∞` against a vector in `ℓ¹`.
example : (lpDualPairing (𝕜 := ℝ) (ι := ℕ) (p := 1) (q := ⊤))
    (lp.single ⊤ 0 (2 : ℝ)) (lp.single 1 0 (1 / 2 : ℝ)) = 1 := by
  rw [lpDualPairing_apply]
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

-- The `p = 1`, `q = ⊤` endpoint: the pairing is norm-preserving. This
-- instantiates `lpDualPairing_norm` (hence the endpoint branch of `exists_coeff`)
-- at the endpoint, unlike the pairing-value test above.
example : ‖lpDualPairing (𝕜 := ℝ) (ι := ℕ) (p := 1) (q := ⊤)
    (lp.single ⊤ 0 (2 : ℝ))‖ = 2 := by
  rw [lpDualPairing_norm (by simp : (1 : ℝ≥0∞) ≠ ⊤),
    lp.norm_single (by simp : (0 : ℝ≥0∞) < ⊤)]
  rw [Real.norm_eq_abs]
  norm_num

-- The complex `ℓ²` case: the pairing is `(3 : ℂ) * I`.
example : (lpDualPairing (𝕜 := ℂ) (ι := ℕ) (p := 2) (q := 2))
    (lp.single 2 0 (3 : ℂ)) (lp.single 2 0 (Complex.I : ℂ)) = 3 * Complex.I := by
  rw [lpDualPairing_apply]
  rw [tsum_eq_single 0]
  · simp
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    simp

end MathlibExtTest.Analysis.Normed.Lp.Dual
