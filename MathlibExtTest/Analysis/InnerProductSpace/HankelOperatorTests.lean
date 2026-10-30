/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HankelOperator

/-!
# Tests for Hankel operators on `ℓ²(ℕ, 𝕜)` with absolutely summable symbol

The test symbols are the delta symbols `δ₀`, `δ₁` (finitely supported, hence
absolutely summable) and the two-term symbol `δ₀ / 2 + δ₁ / 2`.

* `H_{δ₀}` is the rank-one projection onto `e₀`; `H_{δ₁}` swaps `e₀` and
  `e₁` and kills `e₂, e₃, …`.
* `H_{δ₁}` has operator norm `1` (the bound is sharp on `e₀`, and the
  `ℓ¹`-bound from the main file gives `‖H_{δ₁}‖ ≤ 1`).
* `H_{δ₁}` is self-adjoint (its symbol is real) and compact.
* The two-term symbol acts by the pointwise Hankel formula on `e₀`.
-/

open Set Filter Topology Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.HankelOperator

namespace MathlibExtTest.Analysis.InnerProductSpace.HankelOperatorTests

/-- The delta symbol `δ₀`. -/
private abbrev deltaZero : ℕ → ℂ := fun k => if k = 0 then 1 else 0

/-- The delta symbol `δ₁`. -/
private abbrev deltaOne : ℕ → ℂ := fun k => if k = 1 then 1 else 0

/-- The two-term symbol `δ₀ / 2 + δ₁ / 2`. -/
private noncomputable abbrev deltaTwo : ℕ → ℂ :=
  fun k => if k = 0 then (1 / 2 : ℂ) else if k = 1 then (1 / 2 : ℂ) else 0

/-- The delta symbol `δ₀` is absolutely summable. -/
private theorem summable_norm_delta_zero :
    Summable fun k => ‖deltaZero k‖ := by
  refine summable_of_ne_finset_zero (s := {0}) ?_
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [deltaZero, hi]

/-- The delta symbol `δ₁` is absolutely summable. -/
private theorem summable_norm_delta_one :
    Summable fun k => ‖deltaOne k‖ := by
  refine summable_of_ne_finset_zero (s := {1}) ?_
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [deltaOne, hi]

/-- The two-term symbol `δ₀ / 2 + δ₁ / 2` is absolutely summable. -/
private theorem summable_norm_two_term :
    Summable fun k => ‖deltaTwo k‖ := by
  refine summable_of_ne_finset_zero (s := {0, 1}) ?_
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [deltaTwo, hi.1, hi.2]

/-- The `ℓ¹` norm of `δ₁` is `1`. -/
private theorem tsum_norm_delta_one :
    ∑' k, ‖deltaOne k‖ = 1 := by
  rw [tsum_eq_single 1]
  · simp [deltaOne]
  · intro k hk
    simp [deltaOne, hk]

/-- `H_{δ₀}` fixes `e₀`. -/
example : hankelOperator deltaZero summable_norm_delta_zero
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [deltaZero, lp.single_apply]
  · simp [deltaZero, lp.single_apply, hi]

/-- `H_{δ₀}` kills `e₁`. -/
example : hankelOperator deltaZero summable_norm_delta_zero
    (lp.single 2 1 (1 : ℂ)) = 0 := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 1 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [deltaZero, lp.single_apply]
  · simp [deltaZero, lp.single_apply, hi]

/-- `H_{δ₁}` sends `e₀` to `e₁`. -/
example : hankelOperator deltaOne summable_norm_delta_one
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 1
  · subst hi
    simp [deltaOne, lp.single_apply]
  · simp [deltaOne, lp.single_apply, hi]

/-- `H_{δ₁}` sends `e₁` to `e₀`. -/
example : hankelOperator deltaOne summable_norm_delta_one
    (lp.single 2 1 (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 1 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [deltaOne, lp.single_apply]
  · simp [deltaOne, lp.single_apply, hi]

/-- `H_{δ₁}` kills `e₂`. -/
example : hankelOperator deltaOne summable_norm_delta_one
    (lp.single 2 2 (1 : ℂ)) = 0 := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 2 (fun j hj => by simp [lp.single_apply, hj])]
  have h1 : i + 2 ≠ 1 := by omega
  simp [deltaOne, lp.single_apply, h1]

/-- `H_{δ₁}` is an involution on `span {e₀, e₁}`: applying it twice to `e₀`
gives `e₀` back. -/
example : (hankelOperator deltaOne summable_norm_delta_one ∘L
    hankelOperator deltaOne summable_norm_delta_one)
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 0 (1 : ℂ) := by
  rw [ContinuousLinearMap.comp_apply]
  have h1 : hankelOperator deltaOne summable_norm_delta_one
      (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
    apply lp.ext
    funext i
    rw [hankelOperator_apply,
      tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
    by_cases hi : i = 1
    · subst hi
      simp [deltaOne, lp.single_apply]
    · simp [deltaOne, lp.single_apply, hi]
  rw [h1]
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 1 (fun j hj => by simp [lp.single_apply, hj])]
  by_cases hi : i = 0
  · subst hi
    simp [deltaOne, lp.single_apply]
  · simp [deltaOne, lp.single_apply, hi]

/-- The operator norm of `H_{δ₁}` is exactly `1`. -/
example : ‖hankelOperator deltaOne summable_norm_delta_one‖ = 1 := by
  apply le_antisymm
  · calc ‖hankelOperator deltaOne summable_norm_delta_one‖
        ≤ ∑' k, ‖deltaOne k‖ :=
          norm_hankelOperator_le summable_norm_delta_one
      _ = 1 := tsum_norm_delta_one
  · have hle := (hankelOperator deltaOne summable_norm_delta_one).le_opNorm
      (lp.single 2 0 (1 : ℂ))
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at hle
    have hact : hankelOperator deltaOne summable_norm_delta_one
        (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
      apply lp.ext
      funext i
      rw [hankelOperator_apply,
        tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
      by_cases hi : i = 1
      · subst hi
        simp [deltaOne, lp.single_apply]
      · simp [deltaOne, lp.single_apply, hi]
    rw [hact] at hle
    simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one,
      mul_one] at hle
    exact hle

/-- `H_{δ₁}` is self-adjoint: its symbol is real-valued. -/
example : IsSelfAdjoint
    (hankelOperator deltaOne summable_norm_delta_one) := by
  apply isSelfAdjoint_hankelOperator_of_forall_star summable_norm_delta_one
  intro k
  rcases eq_or_ne k 1 with rfl | hk
  · simp [deltaOne]
  · simp [deltaOne, hk]

/-- `H_{δ₀}` is compact. -/
example : IsCompactOperator
    (hankelOperator deltaZero summable_norm_delta_zero) :=
  isCompactOperator_hankelOperator summable_norm_delta_zero

/-- `H_{δ₁}` is compact. -/
example : IsCompactOperator
    (hankelOperator deltaOne summable_norm_delta_one) :=
  isCompactOperator_hankelOperator summable_norm_delta_one

/-- The two-term symbol acts on `e₀` by the Hankel formula:
`Hₐ e₀ = (1/2) • e₀ + (1/2) • e₁`. -/
example : hankelOperator deltaTwo summable_norm_two_term (lp.single 2 0 (1 : ℂ)) =
      (1 / 2 : ℂ) • lp.single 2 0 (1 : ℂ) + (1 / 2 : ℂ) • lp.single 2 1 (1 : ℂ) := by
  apply lp.ext
  funext i
  rw [hankelOperator_apply,
    tsum_eq_single 0 (fun j hj => by simp [lp.single_apply, hj])]
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul,
    Pi.smul_apply]
  by_cases hi0 : i = 0
  · subst hi0
    simp [deltaTwo, lp.single_apply]
  · by_cases hi1 : i = 1
    · subst hi1
      simp [deltaTwo, lp.single_apply]
    · simp [deltaTwo, lp.single_apply, hi0, hi1]

/-- The zero symbol gives the zero operator. -/
example : hankelOperator (0 : ℕ → ℂ) (by simp) = 0 :=
  hankelOperator_zero

end MathlibExtTest.Analysis.InnerProductSpace.HankelOperatorTests
