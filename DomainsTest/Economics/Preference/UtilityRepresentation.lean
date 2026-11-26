/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Preference.UtilityRepresentation
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
import Domains.Economics.Preference.OrdinalInvariance

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

private theorem tiePref_counts : tiePref.lowerContourCount = ![3, 3, 1] := by
  let : DecidableRel tiePref.R := fun _ _ => Nat.decLe _ _
  have h : ∀ x : Fin 3, (Finset.univ.filter (tiePref.R x)).card =
      (![3, 3, 1] : Fin 3 → ℕ) x := by decide
  funext x
  rw [Preference.lowerContourCount, Set.Finite.toFinset_ofPred]
  exact h x

example :
    tiePref.Indiff 0 1 ∧ tiePref.lowerContourCount 0 = tiePref.lowerContourCount 1 ∧
      tiePref.StrictPref 0 2 ∧ tiePref.lowerContourCount 2 < tiePref.lowerContourCount 0 := by
  have hcmp (x y : Fin 3) :
      tiePref.R x y ↔ tiePref.lowerContourCount y ≤ tiePref.lowerContourCount x :=
    (tiePref.represents_lowerContourCount x y).trans Nat.cast_le
  rw [tiePref_counts] at hcmp ⊢
  exact ⟨⟨(hcmp 0 1).2 (by decide), (hcmp 1 0).2 (by decide)⟩, by decide,
    ⟨(hcmp 0 2).2 (by decide), fun h => (by decide : ¬ (3 : ℕ) ≤ 1) ((hcmp 2 0).1 h)⟩,
    by decide⟩

example :
    let A : Set (Fin 3) := {0, 2}
    tiePref.choice A = {0} ∧
      (utilityChoice (fun x => (tiePref.lowerContourCount x : ℝ)) A).Nonempty := by
  let A : Set (Fin 3) := {0, 2}
  have hchoice := tiePref.represents_lowerContourCount.choice_eq_utilityChoice A
  refine ⟨hchoice.trans ?_, hchoice ▸ tiePref.choice_nonempty (Set.toFinite A) ⟨0, Or.inl rfl⟩⟩
  ext x
  simp only [utilityChoice, A, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    tiePref_counts, Nat.cast_le]
  revert x
  decide

example : tiePref.choice ({0, 1} : Set (Fin 3)) = {0, 1} := by
  rw [tiePref.represents_lowerContourCount.choice_eq_utilityChoice]
  ext x
  simp only [utilityChoice, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    tiePref_counts, Nat.cast_le]
  revert x
  decide

end PreferenceExamples

end MathlibExtTest.Economics.Preference.UtilityRepresentation
