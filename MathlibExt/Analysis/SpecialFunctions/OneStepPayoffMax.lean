/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# One-step payoff maximisation

Fix real numbers `m₋`, `m₊` and `b > 0`, and write `D = m₊ - m₋`. For a nonnegative stake `a`,
consider the finite payoff
`F(a) = -a + (a m₊ + b m₋) / (a + b) = m₊ - a - b D / (a + b)`.
Over `a ≥ 0` it has the unique maximiser `s = max 0 (√(b D) - b)`, for every real `D`:

* if `D > b`, then `s = √(b D) - b > 0` is interior;
* if `D = b`, then `s = 0` is a boundary point where the first-order equation still holds;
* if `0 < D < b` or `D ≤ 0`, then `s = 0` (for `D ≤ 0`, `Real.sqrt` of the nonpositive number
  `b D` is `0`).

The first-order equation `(s + b)² = b D` holds at the maximiser exactly when `D ≥ b`.

The proof is algebraic, through two gap identities: for every real `D`,
`F(0) - F(a) = a (a + b - D) / (a + b)`, and if `c² = b D` with `c ≥ b`, then
`F(c - b) - F(a) = (a + b - c)² / (a + b)`. No differentiation is used.

## Main results

* `payoff_le_of_eq_max_sqrt`: `s` maximises `F` over `a ≥ 0`, and it is the only maximiser.
* `sq_eq_mul_iff_of_eq_max_sqrt`: `(s + b)² = b D` if and only if `b ≤ D`.
-/

@[expose] public section

namespace MathlibExt.Analysis.SpecialFunctions.OneStepPayoffMax

variable {mMinus mPlus b a : ℝ}

/-- The payoff in the form `m₊ - a - b D / (a + b)`. -/
private theorem payoff_eq (hb : 0 < b) (ha : 0 ≤ a) :
    -a + (a * mPlus + b * mMinus) / (a + b) = mPlus - a - b * (mPlus - mMinus) / (a + b) := by
  have : a + b ≠ 0 := by positivity
  field_simp
  ring

/-- The gap to the zero stake, for every real `D`. -/
private theorem payoff_zero_sub (hb : 0 < b) (ha : 0 ≤ a) :
    (-0 + (0 * mPlus + b * mMinus) / (0 + b)) - (-a + (a * mPlus + b * mMinus) / (a + b)) =
      a * (a + b - (mPlus - mMinus)) / (a + b) := by
  rw [payoff_eq hb le_rfl, payoff_eq hb ha]
  have : a + b ≠ 0 := by positivity
  have : b ≠ 0 := hb.ne'
  field_simp
  ring

/-- The gap to the stake `c - b`, where `c² = b D` and `b ≤ c`. -/
private theorem payoff_sub_sub_of_sq_eq {c : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hcb : b ≤ c)
    (hc : c ^ 2 = b * (mPlus - mMinus)) :
    (-(c - b) + ((c - b) * mPlus + b * mMinus) / (c - b + b)) -
        (-a + (a * mPlus + b * mMinus) / (a + b)) = (a + b - c) ^ 2 / (a + b) := by
  rw [payoff_eq hb (by linarith), payoff_eq hb ha, ← hc]
  have : a + b ≠ 0 := by positivity
  have : c - b + b ≠ 0 := by linarith
  field_simp
  ring

private theorem max_sqrt_eq_zero (hb : 0 < b) (hD : mPlus - mMinus ≤ b) :
    max 0 (Real.sqrt (b * (mPlus - mMinus)) - b) = 0 := by
  have : Real.sqrt (b * (mPlus - mMinus)) ≤ b := by
    rw [Real.sqrt_le_left hb.le]
    nlinarith
  simp [this]

private theorem le_sqrt_of_le (hb : 0 < b) (hD : b ≤ mPlus - mMinus) :
    b ≤ Real.sqrt (b * (mPlus - mMinus)) :=
  Real.le_sqrt_of_sq_le (by nlinarith)

private theorem max_sqrt_eq (hb : 0 < b) (hD : b ≤ mPlus - mMinus) :
    max 0 (Real.sqrt (b * (mPlus - mMinus)) - b) = Real.sqrt (b * (mPlus - mMinus)) - b := by
  simp [le_sqrt_of_le hb hD]

/-- **The one-step payoff has a unique maximiser.** Let `b > 0`, `D = m₊ - m₋` be any real
number, and `s = max 0 (√(b D) - b)`. For every stake `a ≥ 0`, the payoff
`F(a) = -a + (a m₊ + b m₋) / (a + b)` satisfies `F(a) ≤ F(s)`, and `F(a) = F(s)` only if
`a = s`. The maximiser is interior when `D > b` and is `0` when `D ≤ b`. -/
theorem payoff_le_of_eq_max_sqrt {mMinus mPlus b a s : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) :
    -a + (a * mPlus + b * mMinus) / (a + b) ≤ -s + (s * mPlus + b * mMinus) / (s + b) ∧
      (-a + (a * mPlus + b * mMinus) / (a + b) = -s + (s * mPlus + b * mMinus) / (s + b) →
        a = s) := by
  have hpos : 0 < a + b := by positivity
  rcases le_total (mPlus - mMinus) b with hD | hD
  · rw [max_sqrt_eq_zero hb hD] at hs
    subst hs
    have hg := payoff_zero_sub (mMinus := mMinus) (mPlus := mPlus) hb ha
    refine ⟨?_, fun h => ?_⟩
    · have : 0 ≤ a * (a + b - (mPlus - mMinus)) / (a + b) :=
        div_nonneg (mul_nonneg ha (by linarith)) hpos.le
      linarith
    · rw [← h, sub_self] at hg
      rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hg.symm).resolve_right hpos.ne') with h0 | h0
      · exact h0
      · linarith
  · rw [max_sqrt_eq hb hD] at hs
    subst hs
    have hg := payoff_sub_sub_of_sq_eq (a := a) hb ha (le_sqrt_of_le hb hD)
      (Real.sq_sqrt (by nlinarith))
    refine ⟨?_, fun h => ?_⟩
    · have := div_nonneg (sq_nonneg (a + b - Real.sqrt (b * (mPlus - mMinus)))) hpos.le
      linarith
    · rw [← h, sub_self] at hg
      have h0 := (div_eq_zero_iff.mp hg.symm).resolve_right hpos.ne'
      have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h0
      linarith

/-- **The first-order equation holds at the maximiser exactly when `D ≥ b`.** Let `b > 0`,
`D = m₊ - m₋` be any real number, and `s = max 0 (√(b D) - b)`. Then `(s + b)² = b D` if and
only if `b ≤ D`; this includes the boundary case `D = b`, where `s = 0`. This is the algebraic
equation, not a statement about derivatives. -/
theorem sq_eq_mul_iff_of_eq_max_sqrt {mMinus mPlus b s : ℝ} (hb : 0 < b)
    (hs : s = max 0 (Real.sqrt (b * (mPlus - mMinus)) - b)) :
    (s + b) ^ 2 = b * (mPlus - mMinus) ↔ b ≤ mPlus - mMinus := by
  constructor
  · intro h
    by_contra hD
    rw [max_sqrt_eq_zero hb (not_le.mp hD).le] at hs
    rw [hs, zero_add] at h
    nlinarith [not_le.mp hD]
  · intro hD
    rw [hs, max_sqrt_eq hb hD, sub_add_cancel, Real.sq_sqrt (by nlinarith)]

end MathlibExt.Analysis.SpecialFunctions.OneStepPayoffMax
