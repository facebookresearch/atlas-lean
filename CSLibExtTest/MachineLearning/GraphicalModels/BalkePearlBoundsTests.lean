/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BalkePearlBounds
import MathlibExt.Analysis.Convex.StdSimplexWeights
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BalkePearl

/-- The terms of eq. (4) on the vitamin A data, as printed in Balke and Pearl (1997),
Section 4.1. -/
example : (List.ofFn (lowerTerms vitaminA)) =
    [-0.1946, -0.1982, -0.9972, -0.9936, -0.9910, -1.9898, -0.2018, -0.3928] := by
  simp [List.ofFn_succ, lowerTerms, vitaminA]
  norm_num

/-- The terms of eq. (5) on the vitamin A data, as printed there. -/
example : (List.ofFn (upperTerms vitaminA)) =
    [0.0054, 0.8028, 0.0064, 0.8018, 0.0102, 0.0090, 0.8072, 1.5982] := by
  simp [List.ofFn_succ, upperTerms, vitaminA]
  norm_num

/-- Type weights attaining the lower bound on the vitamin A data: almost 80% compliers who survive
either way (`(1,3)`) and almost 20% never-takers whom the supplement would kill (`(0,2)`). -/
noncomputable def vitaminALower : RespType → ℝ := fun t =>
  (![![7/2500, 0, 493/2500, 0], ![1/1000, 13/5000, 0, 1991/2500], ![0, 0, 0, 0],
    ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℝ) t.1 t.2

/-- Type weights attaining the upper bound: `vitaminALower` with the never-takers' outcome types
`0` and `2` replaced by `1` and `3`. -/
noncomputable def vitaminAUpper : RespType → ℝ := fun t =>
  (![![0, 7/2500, 0, 493/2500], ![1/1000, 13/5000, 0, 1991/2500], ![0, 0, 0, 0],
    ![0, 0, 0, 0]] : Fin 4 → Fin 4 → ℝ) t.1 t.2

/-- `vitaminALower` is a type law in the fiber of the vitamin A data, with ACE `-0.1946`. -/
example : ∃ q ∈ fiber vitaminA, (∀ t, q.weights t = vitaminALower t) ∧ q.ace = -0.1946 := by
  have h0 : ∀ t, 0 ≤ vitaminALower t := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> norm_num [vitaminALower]
  have h1 : ∑ t, vitaminALower t = 1 := by
    rw [sum_weights_eq]
    norm_num [vitaminALower]
  have hwt : ∀ t, (Convexity.StdSimplex.ofWeights vitaminALower h0 h1).weights t =
      vitaminALower t :=
    fun t => Convexity.StdSimplex.ofWeights_weights _ _ _ t
  have hweq := funext hwt
  refine ⟨Convexity.StdSimplex.ofWeights vitaminALower h0 h1, ?_, hwt, ?_⟩
  · show TypeLaw.obs (Convexity.StdSimplex.ofWeights vitaminALower h0 h1) = vitaminA
    have hobs : TypeLaw.obs (Convexity.StdSimplex.ofWeights vitaminALower h0 h1) =
        obsForm vitaminALower := by
      unfold TypeLaw.obs
      rw [hweq]
    rw [hobs]
    funext y d z
    cases y <;> cases d <;> cases z <;>
      simp [obsForm_fff, obsForm_fft, obsForm_ftf, obsForm_ftt, obsForm_tff, obsForm_tft,
        obsForm_ttf, obsForm_ttt, vitaminALower, vitaminA] <;>
      norm_num
  · show TypeLaw.ace (Convexity.StdSimplex.ofWeights vitaminALower h0 h1) = -0.1946
    have hace : TypeLaw.ace (Convexity.StdSimplex.ofWeights vitaminALower h0 h1) =
        aceForm vitaminALower := by
      unfold TypeLaw.ace
      rw [hweq]
    rw [hace, aceForm_eq]
    norm_num [vitaminALower]

/-- `vitaminAUpper` is a type law in the fiber of the vitamin A data, with ACE `0.0054`. -/
example : ∃ q ∈ fiber vitaminA, (∀ t, q.weights t = vitaminAUpper t) ∧ q.ace = 0.0054 := by
  have h0 : ∀ t, 0 ≤ vitaminAUpper t := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> norm_num [vitaminAUpper]
  have h1 : ∑ t, vitaminAUpper t = 1 := by
    rw [sum_weights_eq]
    norm_num [vitaminAUpper]
  have hwt : ∀ t, (Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1).weights t =
      vitaminAUpper t :=
    fun t => Convexity.StdSimplex.ofWeights_weights _ _ _ t
  have hweq := funext hwt
  refine ⟨Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1, ?_, hwt, ?_⟩
  · show TypeLaw.obs (Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1) = vitaminA
    have hobs : TypeLaw.obs (Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1) =
        obsForm vitaminAUpper := by
      unfold TypeLaw.obs
      rw [hweq]
    rw [hobs]
    funext y d z
    cases y <;> cases d <;> cases z <;>
      simp [obsForm_fff, obsForm_fft, obsForm_ftf, obsForm_ftt, obsForm_tff, obsForm_tft,
        obsForm_ttf, obsForm_ttt, vitaminAUpper, vitaminA] <;>
      norm_num
  · show TypeLaw.ace (Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1) = 0.0054
    have hace : TypeLaw.ace (Convexity.StdSimplex.ofWeights vitaminAUpper h0 h1) =
        aceForm vitaminAUpper := by
      unfold TypeLaw.ace
      rw [hweq]
    rw [hace, aceForm_eq]
    norm_num [vitaminAUpper]

/-- Every type law generating the vitamin A data has `-0.1946 ≤ ACE ≤ 0.0054`. -/
example (q : TypeLaw) (hq : q ∈ fiber vitaminA) : -0.1946 ≤ q.ace ∧ q.ace ≤ 0.0054 := by
  have hobs : q.obs = vitaminA := hq
  have hlo := lowerBound_le_ace q
  have hhi := ace_le_upperBound q
  rw [hobs] at hlo hhi
  obtain ⟨hlb, hub⟩ := vitaminA_bounds
  rw [hlb] at hlo
  rw [hub] at hhi
  exact ⟨hlo, hhi⟩

/-- An observed law violating the first binary instrumental inequality (`p00.0 + p10.1 = 6/5`). -/
noncomputable def ivViolating : ObsLaw
  | false, false, false => 3 / 5
  | true, false, false => 2 / 5
  | false, false, true => 2 / 5
  | true, false, true => 3 / 5
  | _, _, _ => 0

/-- Ordered bounds do not imply compatibility: at `ivViolating` the closed forms give the interval
`[-1/5, 1/5]`, yet no type law generates it. -/
example : lowerBound ivViolating = -1 / 5 ∧ upperBound ivViolating = 1 / 5 ∧
    ¬ Compatible ivViolating := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [lowerBound]
      refine Finset.sup'_le _ _ ?_
      intro i _
      fin_cases i <;> norm_num [lowerTerms, ivViolating]
    · have h4 : lowerTerms ivViolating 4 = -1 / 5 := by
        norm_num [lowerTerms, ivViolating]
      rw [← h4, lowerBound]
      exact Finset.le_sup' _ (Finset.mem_univ 4)
  · apply le_antisymm
    · have h7 : upperTerms ivViolating 7 = 1 / 5 := by
        norm_num [upperTerms, ivViolating]
      rw [← h7, upperBound]
      exact Finset.inf'_le _ (Finset.mem_univ 7)
    · rw [upperBound]
      refine Finset.le_inf' _ _ ?_
      intro i _
      fin_cases i <;> norm_num [upperTerms, ivViolating]
  · rintro ⟨q, hq⟩
    obtain ⟨h, -, -, -⟩ := instrumental_inequalities q
    have hq' : q.obs = ivViolating := hq
    rw [hq'] at h
    norm_num [ivViolating] at h

end Cslib.MachineLearning.GraphicalModels.BalkePearl
