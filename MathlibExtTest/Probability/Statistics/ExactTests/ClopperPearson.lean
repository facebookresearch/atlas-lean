/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.ClopperPearson

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathlibExt.Probability.Statistics.ExactTests

namespace MathlibExtTest.Probability.Statistics.ExactTests.ClopperPearson

/-! ### `n = 0`: the only observation is `x = 0`, and the interval is `[0, 1]` -/

/-- `n = 0`, `x = 0`: `L = 0` and `U = 1`. -/
example {α : ℝ} (hα : α ≤ 2) :
    clopperPearsonLower 0 0 α = 0 ∧ clopperPearsonUpper 0 0 α = 1 :=
  ⟨clopperPearsonLower_zero 0 hα, clopperPearsonUpper_self 0 hα⟩

/-- `n = 0`: the upper-endpoint tail `P_p(X ≥ 1)` is an empty sum, so `P_p(X ≤ 0) = 1`
computed from Mathlib's `Bin(0, p) = δ₀`. -/
example (p : unitInterval) : (binomial 0 p).real (Iic 0) = 1 := by
  rw [binomial_zero]
  simp

/-! ### `n = 1`: `L(1) = α / 2` and `U(0) = 1 - α / 2` -/

/-- `n = 1`, `x = 1`: `P_p(X ≥ 1) = p`, so `L(1) = α / 2`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : clopperPearsonLower 1 1 α = α / 2 := by
  refine clopperPearsonLower_eq_of_binomTail_eq le_rfl le_rfl ⟨by linarith, by linarith⟩ ?_
  simp [binomTail]

/-- `n = 1`, `x = 0`: `P_p(X ≤ 0) = 1 - p`, so `U(0) = 1 - α / 2`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : clopperPearsonUpper 1 0 α = 1 - α / 2 := by
  refine clopperPearsonUpper_eq_of_binomTail_eq Nat.zero_lt_one ⟨by linarith, by linarith⟩ ?_
  simp [binomTail]

/-- `n = 1`: the boundary endpoints `L(0) = 0` and `U(1) = 1`. -/
example {α : ℝ} (hα1 : α < 1) :
    clopperPearsonLower 1 0 α = 0 ∧ clopperPearsonUpper 1 1 α = 1 :=
  ⟨clopperPearsonLower_zero 1 (by linarith), clopperPearsonUpper_self 1 (by linarith)⟩

/-! ### `n = 3`, `α = 1 / 4` (each tail gets `1 / 8`) -/

/-- `n = 3`, `x = 3`: `P_{1/2}(X ≥ 3) = (1/2)³ = 1/8`, so `L(3) = 1 / 2`. -/
example : clopperPearsonLower 3 3 (1 / 4) = 1 / 2 := by
  refine clopperPearsonLower_eq_of_binomTail_eq (by norm_num) le_rfl ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail]

/-- `n = 3`, `x = 0`: `P_{1/2}(X ≤ 0) = (1/2)³ = 1/8`, computed as `1 - P_{1/2}(X ≥ 1)` with
`P_{1/2}(X ≥ 1) = 3/8 + 3/8 + 1/8`, so `U(0) = 1 / 2`. -/
example : clopperPearsonUpper 3 0 (1 / 4) = 1 / 2 := by
  refine clopperPearsonUpper_eq_of_binomTail_eq (by norm_num) ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- The same tail from Mathlib's binomial masses: `Bin(3, 1/2)({3}) = 1/8`, and this is the
whole upper tail `Bin(3, 1/2)([3, ∞))` at the lower endpoint `L(3) = 1/2`. -/
example : (binomial 3 ⟨1 / 2, by norm_num, by norm_num⟩).real {3} = 1 / 8 ∧
    upperTail (binomial 3 ⟨1 / 2, by norm_num, by norm_num⟩) 3 = 1 / 8 := by
  refine ⟨?_, ?_⟩
  · rw [binomial_real_singleton]
    norm_num
  · rw [upperTail_binomial]
    norm_num [binomTail]

/-- An interior endpoint: `n = 3`, `x = 1`, `α = 122/125`. `P_{1/5}(X ≥ 1) = 1 - (4/5)³ =
61/125 = α / 2`, so `L(1) = 1 / 5`. -/
example : clopperPearsonLower 3 1 (122 / 125) = 1 / 5 := by
  refine clopperPearsonLower_eq_of_binomTail_eq le_rfl (by norm_num) ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- `n = 3`, `x = 1` gives a proper interior interval `0 < L(1) ≤ U(1) < 1`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < clopperPearsonLower 3 1 α ∧ clopperPearsonLower 3 1 α ≤ clopperPearsonUpper 3 1 α ∧
      clopperPearsonUpper 3 1 α < 1 :=
  ⟨(clopperPearsonLower_mem_Ioo le_rfl (by norm_num) hα0 (by linarith)).1,
    clopperPearsonLower_le_clopperPearsonUpper (by norm_num) hα0 hα1.le,
    (clopperPearsonUpper_mem_Ioo (by norm_num) hα0 (by linarith)).2⟩

/-- Test inversion at `n = 3`, `x = 3`, `α = 1/4`: `p = 3/4` is inside the interval because
`P_{3/4}(X ≥ 3) = 27/64 ≥ 1/8`. -/
example : clopperPearsonLower 3 3 (1 / 4) ≤ 3 / 4 := by
  rw [clopperPearsonLower_le_iff le_rfl (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [binomTail]

/-- Test inversion at `n = 3`, `x = 3`, `α = 1/4`: `p = 1/4` is outside the interval because
`P_{1/4}(X ≥ 3) = 1/64 < 1/8`. -/
example : ¬ clopperPearsonLower 3 3 (1 / 4) ≤ 1 / 4 := by
  rw [clopperPearsonLower_le_iff le_rfl (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [binomTail]

/-! ### Coverage -/

/-- The coverage theorem applied to the canonical binomial count (`id` under `Bin(n, p)`). -/
example (n : ℕ) (p : unitInterval) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ (binomial n p).real
      {k | clopperPearsonLower n k α ≤ p ∧ (p : ℝ) ≤ clopperPearsonUpper n k α} :=
  clopperPearson_coverage HasLaw.id hα0 hα1

/-- The one-sided bounds each cover with probability at least `1 - α / 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X (binomial n p) P) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α / 2 ≤ P.real {ω | clopperPearsonLower n (X ω) α ≤ p} ∧
      1 - α / 2 ≤ P.real {ω | (p : ℝ) ≤ clopperPearsonUpper n (X ω) α} :=
  ⟨clopperPearsonLower_coverage hX hα0 hα1, clopperPearsonUpper_coverage hX hα0 hα1⟩

end MathlibExtTest.Probability.Statistics.ExactTests.ClopperPearson
