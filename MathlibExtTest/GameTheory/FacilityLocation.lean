/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.FacilityLocation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.Sort
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Tests for strategyproof facility location

Concrete checks for `MathlibExt.GameTheory.FacilityLocation`: costs (T1),
the leftmost mechanism (T2), the median mechanism (T3), a maximum-cost lower
bound (T4), (non-)strategyproofness examples (T5), and headline theorem
applications (T6). T1-T5 are direct computations.
-/

namespace MathlibExtTest.GameTheory.FacilityLocation

open MathlibExt.GameTheory.FacilityLocation

/-- (T1) Social cost of a three-agent profile at the middle report. -/
public theorem test_socialCost_example :
    socialCost ![0, 10, 20] 10 = 20 := by
  simp [socialCost, Fin.sum_univ_three]
  norm_num

/-- (T1) Maximum cost of a three-agent profile at the middle report. -/
public theorem test_maxCost_example :
    maxCost ![0, 10, 20] 10 = 10 := by
  apply le_antisymm
  · apply maxCost_le
    intro i
    fin_cases i
    · norm_num [Matrix.cons_val_zero]
    · norm_num [Matrix.cons_val_one, Matrix.cons_val_zero]
    · norm_num [Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_zero]
  · have h := le_maxCost ![0, 10, 20] 10 0
    simp only [Matrix.cons_val_zero] at h
    norm_num at h
    exact h

/-- (T1) Maximum cost of a two-agent profile at the midpoint. -/
public theorem test_maxCost_half :
    maxCost ![0, 1] (1 / 2) = 1 / 2 := by
  apply le_antisymm
  · apply maxCost_le
    intro i
    fin_cases i
    · norm_num [Matrix.cons_val_zero]
    · norm_num [Matrix.cons_val_one, Matrix.cons_val_zero]
  · have h := le_maxCost ![0, 1] (1 / 2) 0
    simp only [Matrix.cons_val_zero] at h
    norm_num at h
    exact h

/-- (T2) The leftmost mechanism outputs the minimum report. -/
public theorem test_leftmost_example :
    leftmost ![3, 1, 4] = 1 := by
  have h1 : leftmost ![3, 1, 4] ≤ 1 := by
    have h := leftmost_le ![3, 1, 4] 1
    simpa using h
  obtain ⟨i, hi⟩ := leftmost_exists ![3, 1, 4]
  fin_cases i
  · simp at hi
    simp at h1
    linarith
  · simpa using hi
  · simp at hi
    simp at h1
    linarith

/-- (T3) The median of three reports is the middle one. -/
public theorem test_median_three :
    median ![0, 10, 20] = 10 := by
  have hof : List.ofFn ![0, 10, 20] = [(0 : ℝ), 10, 20] := by
    simp [List.ofFn_succ, List.ofFn_zero]
  have hsort :
      List.insertionSort (· ≤ ·) [(0 : ℝ), 10, 20] = [(0 : ℝ), 10, 20] := by
    apply List.Pairwise.insertionSort_eq
    simp only [List.pairwise_cons, List.mem_cons]
    norm_num
  have hlist : List.insertionSort (· ≤ ·) (List.ofFn ![0, 10, 20])
      = [(0 : ℝ), 10, 20] := by
    rw [hof, hsort]
  have hmain : ∀ (l : List ℝ) (h : (3 - 1) / 2 < l.length),
      l = [(0 : ℝ), 10, 20] → l.get ⟨(3 - 1) / 2, h⟩ = 10 := by
    intro l h heq
    subst heq
    rfl
  unfold median
  exact hmain _ _ hlist

/-- (T3) The lower median of four reports is the second smallest. -/
public theorem test_median_four :
    median ![0, 1, 2, 100] = 1 := by
  have hof : List.ofFn ![0, 1, 2, 100] = [(0 : ℝ), 1, 2, 100] := by
    simp [List.ofFn_succ, List.ofFn_zero]
  have hsort :
      List.insertionSort (· ≤ ·) [(0 : ℝ), 1, 2, 100]
        = [(0 : ℝ), 1, 2, 100] := by
    apply List.Pairwise.insertionSort_eq
    simp only [List.pairwise_cons, List.mem_cons]
    norm_num
  have hlist : List.insertionSort (· ≤ ·) (List.ofFn ![0, 1, 2, 100])
      = [(0 : ℝ), 1, 2, 100] := by
    rw [hof, hsort]
  have hmain : ∀ (l : List ℝ) (h : (4 - 1) / 2 < l.length),
      l = [(0 : ℝ), 1, 2, 100] → l.get ⟨(4 - 1) / 2, h⟩ = 1 := by
    intro l h heq
    subst heq
    rfl
  unfold median
  exact hmain _ _ hlist

/-- (T4) Every point is at distance at least `1/2` from `0` or `1`. -/
public theorem test_maxCost_half_lower :
    ∀ y : ℝ, (1 / 2 : ℝ) ≤ maxCost ![0, 1] y := by
  intro y
  by_contra hcon
  push Not at hcon
  have h0 := le_maxCost ![0, 1] y 0
  have h1 := le_maxCost ![0, 1] y 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [sub_zero] at h0
  have htri := abs_add_le (1 - y) y
  norm_num at htri
  rw [abs_sub_comm (1 : ℝ) y] at htri
  linarith [h0, h1, hcon, htri]

/-- (T5) A constant mechanism is strategyproof. -/
public theorem test_const_isStrategyproof :
    IsStrategyproof (fun _ : Fin 2 → ℝ => (0 : ℝ)) := by
  intro x i r
  exact le_refl _

/-- (T5) The mechanism `x ↦ x 0 + 1` is not strategyproof: at profile
`![0, 0]`, agent `0` profits by reporting `-1`. -/
public theorem test_shift_not_strategyproof :
    ¬ IsStrategyproof (fun x : Fin 2 → ℝ => x 0 + 1) := by
  intro h
  have hdev := h ![0, 0] 0 (-1)
  simp only [Matrix.cons_val_zero, Function.update_self] at hdev
  norm_num at hdev

/-- (T6) The median-minimizes-social-cost theorem, applied at a profile. -/
public theorem test_median_minimizes_example :
    socialCost ![0, 10, 20] (median ![0, 10, 20]) ≤
      socialCost ![0, 10, 20] 0 :=
  median_minimizes_socialCost _ _

/-- (T6) The median group-strategyproofness theorem, instantiated. -/
public theorem test_median_group_strategyproof :
    IsGroupStrategyproof (median : Mechanism (Fin 3)) :=
  median_isGroupStrategyproof

/-- (T6) Group strategyproofness implies strategyproofness, for the median. -/
public theorem test_median_strategyproof_of_group :
    IsStrategyproof (median : Mechanism (Fin 3)) :=
  isStrategyproof_of_isGroupStrategyproof median_isGroupStrategyproof

/-- (T6) The median strategyproofness theorem, instantiated. -/
public theorem test_median_strategyproof :
    IsStrategyproof (median : Mechanism (Fin 3)) :=
  median_isStrategyproof

/-- (T6) The leftmost strategyproofness theorem, instantiated. -/
public theorem test_leftmost_strategyproof :
    IsStrategyproof (leftmost : Mechanism (Fin 3)) :=
  leftmost_isStrategyproof

/-- (T6) The leftmost 2-approximation theorem, applied at a profile. -/
public theorem test_leftmost_approx_example :
    maxCost ![0, 10] (leftmost ![0, 10]) ≤ 2 * maxCost ![0, 10] 5 :=
  leftmost_isApproxMaxCost_two _ _

/-- (T6) The two-agent lower-bound theorem: no strategyproof mechanism is
a `c`-approximation for `c < 2`. -/
public theorem test_no_strategyproof_better_than_two
    (f : Mechanism (Fin 2)) (hSP : IsStrategyproof f) (c : ℝ)
    (hc : IsApproxMaxCost f c) : ¬ c < 2 :=
  not_lt_of_ge (two_le_of_isStrategyproof_isApproxMaxCost f hSP c hc)
