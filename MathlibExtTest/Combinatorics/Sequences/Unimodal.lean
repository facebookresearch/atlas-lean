/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.Unimodal
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open MathlibExt.Combinatorics.Sequences.Unimodal

namespace MathlibExtTest.Combinatorics.Sequences.Unimodal

/-- The sequence `1, 0, 0, 1`. -/
noncomputable def oneZeroZeroOne : ℕ → ℝ := fun i => if i = 0 ∨ i = 3 then 1 else 0

/-- `1, 0, 0, 1` is log-concave (every `aᵢ₋₁ aᵢ₊₁` vanishes) ... -/
example : IsLogConcave oneZeroZeroOne 3 := by
  intro k hk
  have : k ≤ 1 := by omega
  interval_cases k <;> simp [oneZeroZeroOne]

/-- ... and nonnegative, but not unimodal: the hypothesis "no internal zeros" of
`isUnimodal_of_isLogConcave` cannot be dropped. -/
example : ¬ IsUnimodal oneZeroZeroOne 3 := by
  rintro ⟨j, hj, hup, hdown⟩
  interval_cases j
  · have := hdown 2 (by omega) (by omega); norm_num [oneZeroZeroOne] at this
  · have := hdown 2 (by omega) (by omega); norm_num [oneZeroZeroOne] at this
  · have := hup 0 (by omega); norm_num [oneZeroZeroOne] at this
  · have := hup 0 (by omega); norm_num [oneZeroZeroOne] at this

/-- The hypotheses of `isUnimodal_of_isLogConcave` hold together with a zero at the end:
`1, 1, 0` on indices `0, 1, 2`. -/
example : IsUnimodal (fun i => if i ≤ 1 then (1 : ℝ) else 0) 2 := by
  refine isUnimodal_of_isLogConcave (fun i _ => by split_ifs <;> norm_num) ?_ ?_
  · intro k hk
    have : k = 0 := by omega
    subst this
    simp
  · intro i j k hij hjk hkn _ hk
    interval_cases k <;> interval_cases j <;> simp_all

/-- The fifth row of Pascal's triangle is unimodal. -/
example : IsUnimodal (fun k => ((5 : ℕ).choose k : ℝ)) 5 := choose_isUnimodal 5

/-- Boundary `n = 0`: a one-term sequence is unimodal. -/
example (a : ℕ → ℝ) : IsUnimodal a 0 := ⟨0, le_rfl, fun _ h => absurd h (by omega),
  fun _ _ h => absurd h (by omega)⟩

end MathlibExtTest.Combinatorics.Sequences.Unimodal
