/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Regulatory.GPSMStep
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# GPS M-step tests

Three candidate events with expected read counts `N = (5, 1, 3)` and sparseness `α = 2`: the
middle event is eliminated and the update is `(3/4, 0, 1/4)`; with `α = 0` it is the ordinary
mixture update `(5/9, 1/9, 3/9)`; at the boundary `N j = α` the event is eliminated. When no event
survives (`α = 10`) the total surviving weight is `0` and the update is the junk value `0`
(division by zero), which is why `sum_mStep` assumes a survivor.
-/

namespace Cslib.Bioinformatics.Regulatory.GPS

/-- Expected read counts of three candidate events. -/
noncomputable def N₃ : Fin 3 → ℝ := ![5, 1, 3]

example : mStep 2 N₃ = ![3 / 4, 0, 1 / 4] := by
  funext j
  fin_cases j <;> norm_num [mStep, survivorWeight, N₃, Fin.sum_univ_three]

example : mStep 2 N₃ 1 = 0 := (mStep_eq_zero_iff (j₀ := 0) (by norm_num [N₃]) 1).2
  (by norm_num [N₃])

example : ∑ j, mStep 2 N₃ j = 1 := sum_mStep (j₀ := 0) (by norm_num [N₃])

example : mStep 0 N₃ 0 = 5 / 9 := by
  rw [mStep_zero (fun j => by fin_cases j <;> norm_num [N₃])]
  norm_num [N₃, Fin.sum_univ_three]

/-- Boundary: an event with exactly `α` expected reads is eliminated. -/
example : mStep 3 N₃ 2 = 0 := (mStep_eq_zero_iff (j₀ := 0) (by norm_num [N₃]) 2).2
  (by norm_num [N₃])

/-- Junk value outside the domain: with no survivor the update is `0` everywhere. -/
example : mStep 10 N₃ = 0 := by
  funext j
  fin_cases j <;> norm_num [mStep, survivorWeight, N₃, Fin.sum_univ_three]

/-- The update maximizes the truncated objective against the uniform vector. -/
example : truncatedQ 2 N₃ (fun _ => 1 / 3) ≤ truncatedQ 2 N₃ (mStep 2 N₃) :=
  truncatedQ_le_mStep (j₀ := 0) (by norm_num [N₃]) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_three])

end Cslib.Bioinformatics.Regulatory.GPS
