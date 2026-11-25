/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit error bounds for harmonic numbers

This module gives the quantitative form of ATLAS `NumberTheoryI`, Theorem 18.29
(`H(x) = log x + γ + O(1 / x)`): the centered harmonic error at an integer is at most
`1 / n`, and at a real `x ≥ 2` it is at most `2 / x` at `⌊x⌋₊`.

The asymptotic `O(1 / x)` statement itself is already in MathlibExt as
`Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant`
(`MathlibExt/NumberTheory/Harmonic/Floor.lean`) and is not repeated here; the
pointwise bounds below are the explicit estimates behind it. The limit
`Hₙ - log n → γ` is Mathlib's `Real.tendsto_harmonic_sub_log`.

Both bounds follow by sandwiching `Hₙ - log n` between the two Euler–Mascheroni
sequences: `Hₙ - log (n + 1) < γ < Hₙ - log n`, whose gap is
`log (n + 1) - log n ≤ 1 / n`.
-/

@[expose] public section

namespace Real

/-- **Logarithm gap between a real number and its floor.** For every real $x \ge 1$, the floor
$\lfloor x \rfloor$ of $x$ satisfies $\log x - \log \lfloor x \rfloor \le 1/\lfloor x \rfloor$. -/
theorem log_sub_log_floor_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - Real.log (⌊x⌋₊ : ℝ) ≤ 1 / (⌊x⌋₊ : ℝ) := by
  have hn_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.floor_pos.mpr hx
  calc Real.log x - Real.log (⌊x⌋₊ : ℝ)
      = Real.log (x / (⌊x⌋₊ : ℝ)) := by
        rw [Real.log_div (by linarith) (ne_of_gt hn_pos)]
    _ ≤ Real.log (((⌊x⌋₊ : ℝ) + 1) / (⌊x⌋₊ : ℝ)) := by
        apply Real.log_le_log (div_pos (by linarith) hn_pos)
        exact div_le_div_of_nonneg_right (Nat.lt_floor_add_one x).le hn_pos.le
    _ = Real.log (1 + 1 / (⌊x⌋₊ : ℝ)) := by
        congr 1
        field_simp
    _ ≤ 1 / (⌊x⌋₊ : ℝ) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 1 + 1 / (⌊x⌋₊ : ℝ) by positivity)
        linarith

/-- **Explicit harmonic error bound at integers.** Let $H_n = \sum_{k=1}^{n} 1/k$ be the $n$-th
harmonic number and $\gamma$ the Euler–Mascheroni constant. For every natural number $n \ge 1$,
$|H_n - \log n - \gamma| \le 1/n$. -/
theorem abs_harmonic_sub_log_sub_eulerMascheroniConstant_le {n : ℕ} (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ 1 / n := by
  have hn_ne : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hn_pos)]
    have h : ((n : ℝ) + 1) / n = 1 + 1 / (n : ℝ) := by field_simp
    rw [h]
    have h2 := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have hlow := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hup := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  unfold Real.eulerMascheroniSeq at hlow
  simp only [Real.eulerMascheroniSeq', hn_ne, ↓reduceIte] at hup
  rw [abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity]

/-- **Explicit harmonic error bound at real arguments.** Let $H_n = \sum_{k=1}^{n} 1/k$ be the
$n$-th harmonic number and $\gamma$ the Euler–Mascheroni constant. For every real $x \ge 2$,
with $\lfloor x \rfloor$ the floor of $x$, $|H_{\lfloor x \rfloor} - \log x - \gamma| \le 2/x$. -/
theorem abs_harmonic_floor_sub_log_sub_eulerMascheroniConstant_le {x : ℝ} (hx : 2 ≤ x) :
    |(harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant| ≤ 2 / x := by
  have hx1 : 1 ≤ x := by linarith
  have hx_pos : (0 : ℝ) < x := by linarith
  have hn : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx1
  have hn_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have h1 := abs_harmonic_sub_log_sub_eulerMascheroniConstant_le (n := ⌊x⌋₊) hn
  have h2 := log_sub_log_floor_le hx1
  have hlog_le : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hn_pos (Nat.floor_le (by linarith))
  have hA_nonneg :
      0 ≤ (harmonic ⌊x⌋₊ : ℝ) - Real.log (⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' ⌊x⌋₊
    simp only [Real.eulerMascheroniSeq', ne_of_gt hn, ↓reduceIte] at h
    linarith
  have hA_le :
      (harmonic ⌊x⌋₊ : ℝ) - Real.log (⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
        ≤ 1 / (⌊x⌋₊ : ℝ) := (abs_le.mp h1).2
  have hfloor : (1 : ℝ) / (⌊x⌋₊ : ℝ) ≤ 2 / x := by
    rw [div_le_div_iff₀ hn_pos hx_pos]
    have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end Real
