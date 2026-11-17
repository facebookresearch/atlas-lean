/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.WaterFillingCertificate
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open MathlibExt.Analysis.Convex.WaterFillingCertificate Finset

namespace MathlibExtTest.Analysis.Convex.WaterFillingCertificate

/-! ### Validation cases -/

/-- Two unequal positive modes with an inactive low-gain mode: gains `(2, 1, 1/4)`, budget
`3/2`, level `ν = 3/2` (`1/2 + 1 = ν - 1/2 + ν - 1`), allocation `(1, 1/2, 0)`; the third mode is
inactive since `3/2 < 4 = 1 / (1/4)`. -/
theorem waterFilling_twoActive_oneInactive :
    waterLevelSum ![(2 : ℝ), 1, 1 / 4] (3 / 2) = 3 / 2 ∧
      waterFilling ![(2 : ℝ), 1, 1 / 4] (3 / 2) = ![1, 1 / 2, 0] := by
  have g0 : ![(2 : ℝ), 1, 1 / 4] 0 = 2 := rfl
  have g1 : ![(2 : ℝ), 1, 1 / 4] 1 = 1 := rfl
  have g2 : ![(2 : ℝ), 1, 1 / 4] 2 = 1 / 4 := rfl
  have m1 : max ((3 : ℝ) / 2 - 1 / 2) 0 = 1 := by
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2 - 1 / 2)]
    norm_num
  have m2 : max ((3 : ℝ) / 2 - 1 / 1) 0 = 1 / 2 := by
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2 - 1 / 1)]
    norm_num
  have m3 : max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 = 0 :=
    max_eq_right (by norm_num : (3 : ℝ) / 2 - 1 / (1 / 4) ≤ 0)
  have w0 : (if 0 < (2 : ℝ) then max ((3 : ℝ) / 2 - 1 / 2) 0 else 0) = 1 := by
    have hc : (0 : ℝ) < 2 := by norm_num
    simp only [hc, ite_eq_left]
    exact m1
  have w1 : (if 0 < (1 : ℝ) then max ((3 : ℝ) / 2 - 1 / 1) 0 else 0) = 1 / 2 := by
    have hc : (0 : ℝ) < 1 := by norm_num
    simp only [hc, ite_eq_left]
    exact m2
  have w2 : (if 0 < ((1 : ℝ) / 4) then max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 else 0) = 0 := by
    have hc : (0 : ℝ) < 1 / 4 := by norm_num
    simp only [hc, ite_eq_left]
    exact m3
  constructor
  · unfold waterLevelSum
    rw [Finset.sum_filter, Fin.sum_univ_three, g0, g1, g2]
    have c0 : (0 : ℝ) < 2 := by norm_num
    have c1 : (0 : ℝ) < 1 := by norm_num
    have c2 : (0 : ℝ) < 1 / 4 := by norm_num
    simp only [c0, c1, c2, ite_eq_left]
    rw [m1, m2, m3]
    norm_num
  · funext i
    fin_cases i
    · show (if 0 < (2 : ℝ) then max ((3 : ℝ) / 2 - 1 / 2) 0 else 0) = (1 : ℝ)
      exact w0
    · show (if 0 < (1 : ℝ) then max ((3 : ℝ) / 2 - 1 / 1) 0 else 0) = (1 / 2 : ℝ)
      exact w1
    · show (if 0 < ((1 : ℝ) / 4) then max ((3 : ℝ) / 2 - 1 / (1 / 4)) 0 else 0)
          = (0 : ℝ)
      exact w2

/-- The allocation `(1, 1/2, 0)` is optimal for gains `(2, 1, 1/4)` and budget `3/2`. -/
example :
    IsMaxOn (sumRateBits ![(2 : ℝ), 1, 1 / 4]) (powerFeasible (3 / 2)) ![1, 1 / 2, 0] := by
  have h := waterFilling_twoActive_oneInactive
  have hlam : ∀ i, 0 ≤ ![(2 : ℝ), 1, 1 / 4] i := by
    intro i
    fin_cases i
    · show (0 : ℝ) ≤ 2; norm_num
    · show (0 : ℝ) ≤ 1; norm_num
    · show (0 : ℝ) ≤ 1 / 4; norm_num
  rw [← h.2]
  exact (isMaxOn_waterFilling hlam (by norm_num) h.1).2

/-- Its value is `log (3 · 3/2 · 1) / (2 log 2) = log (9/2) / (2 log 2)` bits. -/
theorem sumRateBits_twoActive_oneInactive :
    sumRateBits ![(2 : ℝ), 1, 1 / 4] ![1, 1 / 2, 0] = Real.log (9 / 2) / (2 * Real.log 2) := by
  have g0 : ![(2 : ℝ), 1, 1 / 4] 0 = 2 := rfl
  have g1 : ![(2 : ℝ), 1, 1 / 4] 1 = 1 := rfl
  have g2 : ![(2 : ℝ), 1, 1 / 4] 2 = 1 / 4 := rfl
  have p0 : ![1, 1 / 2, 0] 0 = (1 : ℝ) := rfl
  have p1 : ![1, 1 / 2, 0] 1 = (1 / 2 : ℝ) := rfl
  have p2 : ![1, 1 / 2, 0] 2 = (0 : ℝ) := rfl
  unfold sumRateBits
  rw [Fin.sum_univ_three, g0, g1, g2, p0, p1, p2]
  have e1 : (1 : ℝ) + 2 * 1 = 3 := by norm_num
  have e2 : (1 : ℝ) + 1 * (1 / 2) = 3 / 2 := by norm_num
  have e3 : (1 : ℝ) + 1 / 4 * 0 = 1 := by norm_num
  rw [e1, e2, e3, Real.log_one, zero_div, add_zero]
  have h92 : (9 : ℝ) / 2 = 3 * (3 / 2) := by norm_num
  rw [h92, Real.log_mul (by norm_num) (by norm_num), add_div]

/-- `P = 0` with positive gains: zero power is optimal. -/
example :
    IsMaxOn (sumRateBits ![(2 : ℝ), 1]) (powerFeasible 0) 0 := by
  exact isMaxOn_zero_of_power_eq_zero _

/-- One zero mode: gains `(1, 0)`, budget `1`, level `ν = 2`; the zero mode gets zero power and
the allocation `(1, 0)` is optimal. -/
theorem isMaxOn_oneZeroMode :
    waterLevelSum ![(1 : ℝ), 0] 2 = 1 ∧ waterFilling ![(1 : ℝ), 0] 2 = ![1, 0] ∧
      IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![1, 0] := by
  have g0 : ![(1 : ℝ), 0] 0 = (1 : ℝ) := rfl
  have g1 : ![(1 : ℝ), 0] 1 = (0 : ℝ) := rfl
  have h1 : waterLevelSum ![(1 : ℝ), 0] 2 = 1 := by
    unfold waterLevelSum
    rw [Finset.sum_filter, Fin.sum_univ_two, g0, g1]
    have c0 : (0 : ℝ) < 1 := by norm_num
    have c1 : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    simp only [c0, ite_eq_left, c1, ite_false]
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ (2 : ℝ) - 1 / 1)]
    norm_num
  have h2 : waterFilling ![(1 : ℝ), 0] 2 = ![1, 0] := by
    funext i
    fin_cases i
    · show (if 0 < (1 : ℝ) then max ((2 : ℝ) - 1 / 1) 0 else 0) = (1 : ℝ)
      have hc : (0 : ℝ) < 1 := by norm_num
      simp only [hc, ite_eq_left]
      rw [max_eq_left (by norm_num : (0 : ℝ) ≤ (2 : ℝ) - 1 / 1)]
      norm_num
    · show (if 0 < (0 : ℝ) then max ((2 : ℝ) - 1 / 0) 0 else 0) = (0 : ℝ)
      have hc : ¬ (0 : ℝ) < 0 := lt_irrefl 0
      simp only [hc, ite_false]
  have hlam : ∀ i, 0 ≤ ![(1 : ℝ), 0] i := by
    intro i
    fin_cases i
    · show (0 : ℝ) ≤ 1; norm_num
    · show (0 : ℝ) ≤ 0; norm_num
  have h3 : IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![1, 0] := by
    have hmain := (isMaxOn_waterFilling hlam (by norm_num) h1).2
    rwa [h2] at hmain
  exact ⟨h1, h2, h3⟩

/-- All modes zero: with budget `1`, zero power is optimal. -/
theorem isMaxOn_allZeroModes :
    IsMaxOn (sumRateBits (0 : Fin 2 → ℝ)) (powerFeasible 1) 0 := by
  exact (isMaxOn_zero_of_forall_lam_eq_zero (fun i => rfl) (by norm_num)).2

/-- Violated premise (the inverse formula evaluated at a zero gain): for gains `(1, 0)` and budget
`1`, the unguarded equation `∑ i, max (ν - 1 / lam i) 0 = 1` over all modes (with Lean's
`1 / 0 = 0`) is solved by `ν = 1` and allocates `(0, 1)`, all power on the zero mode; that
allocation is not optimal. -/
theorem unguarded_waterFilling_not_isMaxOn :
    ∑ i, max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0 = 1 ∧
      (fun i => max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0) = ![0, 1] ∧
      ¬ IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![0, 1] := by
  have g0 : ![(1 : ℝ), 0] 0 = (1 : ℝ) := rfl
  have g1 : ![(1 : ℝ), 0] 1 = (0 : ℝ) := rfl
  have q0 : ![0, 1] 0 = (0 : ℝ) := rfl
  have q1 : ![0, 1] 1 = (1 : ℝ) := rfl
  have m1 : max ((1 : ℝ) - 1 / 1) 0 = 0 :=
    max_eq_right (by norm_num : (1 : ℝ) - 1 / 1 ≤ 0)
  have m2 : max ((1 : ℝ) - 1 / 0) 0 = 1 := by
    rw [div_zero, sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  have part1 : ∑ i, max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0 = 1 := by
    rw [Fin.sum_univ_two, g0, g1, m1, m2]
    norm_num
  have part2 : (fun i => max ((1 : ℝ) - 1 / ![(1 : ℝ), 0] i) 0) = ![0, 1] := by
    funext i
    fin_cases i
    · show max ((1 : ℝ) - 1 / 1) 0 = (0 : ℝ)
      exact m1
    · show max ((1 : ℝ) - 1 / 0) 0 = (1 : ℝ)
      exact m2
  have part3 : ¬ IsMaxOn (sumRateBits ![(1 : ℝ), 0]) (powerFeasible 1) ![0, 1] := by
    intro hcon
    have hmem : ![(1 : ℝ), 0] ∈ powerFeasible (1 : ℝ) := by
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · show (0 : ℝ) ≤ 1; norm_num
        · show (0 : ℝ) ≤ 0; norm_num
      · rw [Fin.sum_univ_two, g0, g1]
        norm_num
    have hle : sumRateBits ![(1 : ℝ), 0] ![1, 0]
        ≤ sumRateBits ![(1 : ℝ), 0] ![0, 1] := hcon hmem
    have e1 : sumRateBits ![(1 : ℝ), 0] ![1, 0]
        = Real.log 2 / (2 * Real.log 2) := by
      unfold sumRateBits
      rw [Fin.sum_univ_two, g0, g1]
      have a1 : (1 : ℝ) + 1 * 1 = 2 := by norm_num
      have a2 : (1 : ℝ) + 0 * 0 = 1 := by norm_num
      rw [a1, a2, Real.log_one, zero_div, add_zero]
    have e2 : sumRateBits ![(1 : ℝ), 0] ![0, 1] = 0 := by
      unfold sumRateBits
      rw [Fin.sum_univ_two, g0, g1, q0, q1]
      have b1 : (1 : ℝ) + 1 * 0 = 1 := by norm_num
      have b2 : (1 : ℝ) + 0 * 1 = 1 := by norm_num
      rw [b1, b2, Real.log_one, zero_div, add_zero]
    rw [e1, e2] at hle
    have hpos : 0 < Real.log 2 / (2 * Real.log 2) := by
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hC : 0 < 2 * Real.log 2 := by linarith
      exact div_pos hl2 hC
    linarith
  exact ⟨part1, part2, part3⟩


end MathlibExtTest.Analysis.Convex.WaterFillingCertificate
