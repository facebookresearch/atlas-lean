/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.ProperScoring
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Tests for proper scoring rules on two and three outcomes

Each public theorem is applied to concrete beliefs and reports.
`quadraticRule_isStrictlyProper` gives the quadratic gap on two outcomes (P2/P5).
`logScore_lt_of_fullSupport` gives the log-score gap at a full-support pair;
`logScore_disjunction` returns its support-violation disjunct at
`p = (1/2, 1/2)`, `q = (1, 0)`, where the gap fails, and its gap disjunct at
`p = (1/2, 1/2, 0)`, `q = (1/4, 3/4, 0)`, where both have a zero coordinate
(P3/P5). `logRule_notStrictlyProper` and `linearRule_notProper` give their
witnesses' gaps; the first also shows the real log rule is not proper, the
second that the linear rule is not strictly proper (P3n/P4/P5). Separate checks
pin the expected scores of the three rules at the witnesses, and apply the
quadratic rule's strict properness on a finite type with no decidable equality
and to `Convexity.StdSimplex` weights (P1/P2).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.ProperScoring

open scoped BigOperators
open MathlibExt.GameTheory.ProperScoring
open MathlibExt.GameTheory.Regret (IsSimplex isSimplex_iff)

/-! ### Points of the simplex used below -/

private theorem isSimplex_half : IsSimplex (fun _ : Fin 2 => (1 / 2 : ℝ)) :=
  (isSimplex_iff _).mpr ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two]⟩

private theorem isSimplex_dirac :
    IsSimplex (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) :=
  (isSimplex_iff _).mpr
    ⟨Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩, by norm_num [Fin.sum_univ_two]⟩

private theorem isSimplex_quarter :
    IsSimplex (fun i : Fin 2 => if i = 0 then (1 / 4 : ℝ) else 3 / 4) :=
  (isSimplex_iff _).mpr
    ⟨Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩, by norm_num [Fin.sum_univ_two]⟩

private theorem isSimplex_ternary_p : IsSimplex ![(1 / 2 : ℝ), 1 / 2, 0] :=
  (isSimplex_iff _).mpr ⟨fun i => by fin_cases i <;> norm_num, by
    norm_num [Fin.sum_univ_three]⟩

private theorem isSimplex_ternary_q : IsSimplex ![(1 / 4 : ℝ), 3 / 4, 0] :=
  (isSimplex_iff _).mpr ⟨fun i => by fin_cases i <;> norm_num, by
    norm_num [Fin.sum_univ_three]⟩

/-! ### Quadratic rule (P2/P5) -/

/-- P2/P5: expected quadratic scores at the belief `p = (1/2, 1/2)`: `1/4` for
the truthful report and `0` for the report `q = (1, 0)`. -/
theorem quadratic_binary_values :
    expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) = 1 / 4 ∧
      expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) = 0 := by
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  constructor
  · simp only [expectedScore, quadraticRule, Fin.sum_univ_two]
    norm_num
  · simp only [expectedScore, quadraticRule, Fin.sum_univ_two, hq0, hq1]
    norm_num

/-- P2/P5: strict properness of the quadratic rule gives the strict gap at
`p = (1/2, 1/2)`, `q = (1, 0)`. -/
theorem quadratic_binary_gap :
    expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) <
      expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) := by
  obtain ⟨hle, huniq⟩ := quadraticRule_isStrictlyProper (Fin 2)
  refine lt_of_le_of_ne (hle _ _ isSimplex_half isSimplex_dirac) fun h => ?_
  have h0 := congrFun (huniq _ _ isSimplex_half isSimplex_dirac h) 0
  norm_num at h0

/-! ### Log score (P3/P5) -/

/-- P3/P5: `logScore_lt_of_fullSupport` at the full-support pair
`p = (1/2, 1/2)`, `q = (1/4, 3/4)`. -/
theorem logScore_binary_fullSupport :
    ∑ i : Fin 2, (1 / 2 : ℝ) * Real.log (if i = 0 then 1 / 4 else 3 / 4) <
      ∑ _i : Fin 2, (1 / 2 : ℝ) * Real.log (1 / 2) :=
  logScore_lt_of_fullSupport (Fin 2) _ _ isSimplex_half isSimplex_quarter
    (fun h => by have h0 := congrFun h 0; norm_num at h0)
    (Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩)

/-- P3/P5: at `p = (1/2, 1/2)` and `q = (1, 0)` the strict log-score gap fails
(`Real.log 0 = 0`), so `logScore_disjunction` returns its support-violation
disjunct. -/
theorem logScore_binary_supportViolation :
    (∃ i : Fin 2, 0 < (1 / 2 : ℝ) ∧ (if i = 0 then (1 : ℝ) else 0) = 0) ∧
      ¬ (∑ i : Fin 2, (1 / 2 : ℝ) * Real.log (if i = 0 then 1 else 0) <
        ∑ _i : Fin 2, (1 / 2 : ℝ) * Real.log (1 / 2)) := by
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hneg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hgap : ¬ (∑ i : Fin 2, (1 / 2 : ℝ) * Real.log (if i = 0 then 1 else 0) <
      ∑ _i : Fin 2, (1 / 2 : ℝ) * Real.log (1 / 2)) := by
    rw [not_lt]
    simp only [Fin.sum_univ_two, hq0, hq1, Real.log_one, Real.log_zero, mul_zero,
      add_zero]
    linarith
  exact ⟨(logScore_disjunction (Fin 2) _ _ isSimplex_half isSimplex_dirac
    (fun h => by have h0 := congrFun h 0; norm_num at h0)).resolve_right hgap, hgap⟩

/-- P3/P5: `p = (1/2, 1/2, 0)` and `q = (1/4, 3/4, 0)` both have a zero
coordinate, but `q` vanishes only where `p` does, so `logScore_disjunction`
returns the strict log-score gap, which `logScore_lt_of_fullSupport` does not
reach. -/
theorem logScore_ternary_sharedZero :
    ∑ i, ![(1 / 2 : ℝ), 1 / 2, 0] i * Real.log (![1 / 4, 3 / 4, 0] i) <
      ∑ i, ![(1 / 2 : ℝ), 1 / 2, 0] i * Real.log (![1 / 2, 1 / 2, 0] i) := by
  refine (logScore_disjunction (Fin 3) _ _ isSimplex_ternary_p isSimplex_ternary_q
    fun h => ?_).resolve_left ?_
  · have h0 := congrFun h 0
    norm_num at h0
  · rintro ⟨i, hpi, hqi⟩
    revert hpi hqi
    fin_cases i <;> norm_num

/-! ### Real log rule (P3n/P5) -/

/-- P3n/P5: expected real log scores at the belief `p = (1/2, 1/2)`: `log (1/2)`
for the truthful report and `0` for the report `q = (1, 0)`, as
`Real.log 0 = 0`. -/
theorem logRule_binary_values :
    expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) = Real.log (1 / 2) ∧
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) = 0 := by
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  constructor
  · simp only [expectedScore, logRule, Fin.sum_univ_two]
    ring
  · simp only [expectedScore, logRule, Fin.sum_univ_two, hq0, hq1,
      Real.log_one, Real.log_zero]
    ring

/-- P3n/P5: `logRule_notStrictlyProper` gives its witness's strict gap. -/
theorem logRule_binary_gap :
    expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) <
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) :=
  logRule_notStrictlyProper.2

/-- P3n/P5: by that gap, the real log rule is not even proper on the whole
simplex. -/
theorem logRule_binary_notProper : ¬ IsProper (Fin 2) (logRule (Fin 2)) :=
  fun h => (h _ _ isSimplex_half isSimplex_dirac).not_gt logRule_notStrictlyProper.2

/-! ### Linear rule (P4/P5) -/

/-- P4/P5: expected linear scores at the belief `p = (3/4, 1/4)`: `5/8` for the
truthful report and `3/4` for the report `q = (1, 0)`. -/
theorem linear_binary_values :
    expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 3 / 4 else 1 / 4) = 5 / 8 ∧
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 1 else 0) = 3 / 4 := by
  have hp0 : (if True then (3 / 4 : ℝ) else 1 / 4) = 3 / 4 := by simp
  have hp1 : (if (1 : Fin 2) = 0 then (3 / 4 : ℝ) else 1 / 4) = 1 / 4 := by
    simp
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  constructor
  · simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1]
    norm_num
  · simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1, hq0,
      hq1]
    norm_num

/-- P4/P5: `linearRule_notProper` gives its witness's strict gap. -/
theorem linear_binary_gap :
    expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 3 / 4 else 1 / 4) <
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 1 else 0) :=
  linearRule_notProper.2

/-- P4/P5: as the linear rule is not proper, it is not strictly proper. -/
theorem linear_binary_notStrictlyProper :
    ¬ IsStrictlyProper (Fin 2) (linearRule (Fin 2)) :=
  fun h => linearRule_notProper.1 h.1

/-! ### No decidable equality, and `Convexity.StdSimplex` weights (P1/P2) -/

-- The quadratic rule is strictly proper on every finite outcome type, with no
-- decidable equality on the outcomes in scope.
example (X : Type*) [Fintype X] : IsStrictlyProper X (quadraticRule X) :=
  quadraticRule_isStrictlyProper X

-- Beliefs and reports may be the weights of `Convexity.StdSimplex` points.
example (X : Type*) [Fintype X] (p q : Convexity.StdSimplex ℝ X) :
    expectedScore X (quadraticRule X) p.weights q.weights ≤
      expectedScore X (quadraticRule X) p.weights p.weights :=
  (quadraticRule_isStrictlyProper X).1 _ _
    (MathlibExt.GameTheory.Regret.isSimplex_weights p)
    (MathlibExt.GameTheory.Regret.isSimplex_weights q)

end MathlibExtTest.GameTheory.ProperScoring
