/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Preference.UtilityRepresentation
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort

@[expose] public section

open MathlibExt.Economics

namespace MathlibExtTest.Economics.Preference.UtilityRepresentation

namespace PreferenceExamples

/-- Three alternatives ranked by the scores `1, 1, 0`: alternatives `0` and `1` tie at the top. -/
def tiePref : Preference (Fin 3) where
  R x y := (![1, 1, 0] : Fin 3 → ℕ) y ≤ (![1, 1, 0] : Fin 3 → ℕ) x
  complete := by
    intro x y
    exact le_total _ _
  trans := by
    intro x y z h1 h2
    exact le_trans h2 h1

theorem tiePref_exists_represents : ∃ u : Fin 3 → ℝ, tiePref.Represents u := by
  exact Preference.exists_represents tiePref

theorem tiePref_represents :
    tiePref.Represents (fun x => ((![1, 1, 0] : Fin 3 → ℕ) x : ℝ)) := by
  intro x y
  exact Nat.cast_le.symm

/-- A constant utility is weakly monotone for `tiePref` but does not represent it. -/
theorem tiePref_monotone_const (x y : Fin 3) (h : tiePref.R x y) :
    (fun _ : Fin 3 => (0 : ℝ)) y ≤ (fun _ : Fin 3 => (0 : ℝ)) x := by
  exact le_rfl

theorem tiePref_not_represents_const : ¬ tiePref.Represents (fun _ => 0) := by
  intro h
  have hR := (h 2 0).mpr le_rfl
  have hne : ¬ ((![1, 1, 0] : Fin 3 → ℕ) 0 ≤ (![1, 1, 0] : Fin 3 → ℕ) 2) := by
    decide
  exact hne hR

end PreferenceExamples

end MathlibExtTest.Economics.Preference.UtilityRepresentation
