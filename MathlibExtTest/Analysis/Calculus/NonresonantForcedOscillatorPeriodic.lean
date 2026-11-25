/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted

-- Constant forcing at frequency 1/2 has the constant periodic response 4.
example (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (he : ∀ x, deriv (deriv u) x + (1 / 2 : ℝ) ^ 2 * u x = 1)
    (hp : Function.Periodic u (2 * Real.pi)) : u = fun _ => 4 := by
  have hn : ∀ n : ℕ, (1 / 2 : ℝ) ≠ n := by
    intro n
    cases n with
    | zero => norm_num
    | succ n =>
      have h : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
      linarith
  obtain ⟨v, -, hv⟩ :=
    (existsUnique_periodic_solution_and_isBounded_of_ne_natCast (1 / 2) (by norm_num) hn
      (fun _ => 1) continuous_const (fun _ => rfl)).1
  have hh : (fun _ : ℝ => (4 : ℝ)) = v := hv _
    ⟨contDiff_const, fun _ => by norm_num, fun _ => rfl⟩
  exact (hv _ ⟨hu, he, hp⟩).trans hh.symm
