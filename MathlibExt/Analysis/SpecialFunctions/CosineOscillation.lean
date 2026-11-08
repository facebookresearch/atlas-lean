/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Cosine oscillation

The cosine function does not merely move slowly — it also oscillates by a
definite amount on every interval of length `2 * π`. Precisely, for every
`θ` there is a phase shift `φ ∈ (π, 3 * π)` with `|cos θ - cos (θ + φ)| ≥ 1`,
and in scaled form, for every `c` and every positive `K` there is a point
`y ∈ (c + π / K, c + 3 * π / K)` with `|cos (K * c) - cos (K * y)| ≥ 1`.
Mathlib has the complementary Lipschitz estimate
`Real.abs_cos_sub_cos_le : |cos x - cos y| ≤ |x - y|`, but no lower bound
of this form.

## Main results

* `Real.exists_cos_sub_cos_ge_one`: the phase-shift form of the oscillation.
* `Real.exists_cos_oscillation`: the scaled form above, as stated in the book.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Theorem I),
"Section on Derivative (Weierstrass nowhere differentiable function)", and
`v1/Atlas/RealAnalysis/code/Derivatives/Weierstrass.lean`
(`weierstrass_theorem_I`). That theorem is a conjunction: its first part is
the `1`-Lipschitz estimate, already in Mathlib as `Real.abs_cos_sub_cos_le`,
and its second part is the oscillation statement ported here.
-/

@[expose] public section

namespace Real

/-- **Cosine oscillation (phase-shift form).** For every angle `θ` there is a
phase shift `φ` with `π < φ < 3 * π` such that `cos` moves by at least `1`:
`1 ≤ |cos θ - cos (θ + φ)|`. The two candidate shifts are `3 * π / 2` and
`5 * π / 2`, where `cos` takes the values `sin θ` and `-sin θ`; at least one
of `|cos θ - sin θ|` and `|cos θ + sin θ|` is `≥ 1`, since their squares sum
to `2`. -/
theorem exists_cos_sub_cos_ge_one (θ : ℝ) :
    ∃ φ : ℝ, π < φ ∧ φ < 3 * π ∧ 1 ≤ |cos θ - cos (θ + φ)| := by
  have hpi : 0 < π := pi_pos
  have h1 : cos (θ + 3 * π / 2) = sin θ := by
    have h : θ + 3 * π / 2 = θ + π + π / 2 := by ring
    rw [h, cos_add_pi_div_two, sin_add_pi, neg_neg]
  have h2 : cos (θ + 5 * π / 2) = -sin θ := by
    have h : θ + 5 * π / 2 = (θ + 2 * π) + π / 2 := by ring
    rw [h, cos_add_pi_div_two, sin_add_two_pi]
  by_cases hcase : 1 ≤ |cos θ - sin θ|
  · exact ⟨3 * π / 2, by linarith, by linarith, by rw [h1]; exact hcase⟩
  · push Not at hcase
    refine ⟨5 * π / 2, by linarith, by linarith, ?_⟩
    rw [h2, sub_neg_eq_add]
    by_contra hcon
    push Not at hcon
    have hkey : (cos θ - sin θ) ^ 2 + (cos θ + sin θ) ^ 2 = 2 := by
      have h := sin_sq_add_cos_sq θ
      nlinarith
    have hlt1 : (cos θ - sin θ) ^ 2 < 1 :=
      (_root_.sq_lt_one_iff_abs_lt_one _).mpr hcase
    have hlt2 : (cos θ + sin θ) ^ 2 < 1 :=
      (_root_.sq_lt_one_iff_abs_lt_one _).mpr hcon
    linarith

/-- **Cosine oscillation (scaled form, as in the book).** For every `c` and
every positive natural `K`, there is a point `y` in
`(c + π / K, c + 3 * π / K)` with `|cos (K * c) - cos (K * y)| ≥ 1`. This is
the second part of `weierstrass_theorem_I` in v1; it is the estimate that
drives the slope blow-up in the proof that the Weierstrass function is
nowhere differentiable. -/
theorem exists_cos_oscillation (c : ℝ) (K : ℕ) (hK : 0 < K) :
    ∃ y : ℝ, c + π / K < y ∧ y < c + 3 * π / K ∧
      1 ≤ |cos ((K : ℝ) * c) - cos ((K : ℝ) * y)| := by
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  obtain ⟨φ, hφlo, hφhi, hosc⟩ := exists_cos_sub_cos_ge_one ((K : ℝ) * c)
  refine ⟨c + φ / K, ?_, ?_, ?_⟩
  · have h : π / (K : ℝ) < φ / K := by gcongr
    linarith
  · have h : φ / (K : ℝ) < (3 * π) / K := by gcongr
    linarith
  · have hKy : (K : ℝ) * (c + φ / (K : ℝ)) = (K : ℝ) * c + φ := by field_simp
    rw [hKy]
    exact hosc

end Real
