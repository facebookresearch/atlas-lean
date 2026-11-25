/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.FullSibMating
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Regression tests for the full-sib non-identity recurrence -/

namespace Domains.Biology.PopulationGenetics.Classical.FullSibMating

-- The non-inbred, unrelated starting pair gives the first steps of Figure 5.8.
example : nonIdentity 1 1 0 = (1, 1) ∧ nonIdentity 1 1 1 = (1, 3 / 4) ∧
    nonIdentity 1 1 2 = (3 / 4, 5 / 8) ∧ nonIdentity 1 1 3 = (5 / 8, 1 / 2) := by
  norm_num [nonIdentity]

-- Unequal starts distinguish the two parental contributions; the first coordinate can rise.
example : nonIdentity 0 1 0 = (0, 1) ∧ nonIdentity 0 1 1 = (1, 1 / 2) ∧
    nonIdentity 1 0 1 = (0, 1 / 4) ∧ nonIdentity 1 0 2 = (1 / 4, 1 / 8) := by
  norm_num [nonIdentity]

example (t : ℕ) : nonIdentity 0 0 t = (0, 0) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [nonIdentity, ih]

-- The asymmetric founder state exercises both coefficients in the closed form.
example :
    let p : ℝ := (1 + Real.sqrt 5) / 4
    let m : ℝ := (1 - Real.sqrt 5) / 4
    ∀ t : ℕ, (nonIdentity 0 1 t).2 =
      (1 / 2 - m) / (p - m) * p ^ t + (p - 1 / 2) / (p - m) * m ^ t := by
  obtain ⟨_, _, _, _, _, hClosed, _, _⟩ :=
    nonIdentity_formula (h₀ := 0) (k₀ := 1) (by simp) (by simp)
  simpa using hClosed

-- The nonzero hypothesis permits k₀ = 0. Check the coefficient and the generation shift in the
-- normalized within-individual limit against the concrete first-generation value 1/4.
example :
    let p : ℝ := (1 + Real.sqrt 5) / 4
    let m : ℝ := (1 - Real.sqrt 5) / 4
    Filter.Tendsto (fun t ↦ (nonIdentity 1 0 t).1 / p ^ t) Filter.atTop
      (nhds ((1 / 4 / (p - m)) / p)) := by
  obtain ⟨_, _, _, _, _, _, _, hAsymptotic⟩ :=
    nonIdentity_formula (h₀ := 1) (k₀ := 0) (by simp) (by simp)
  obtain ⟨_, _, hWithin⟩ := hAsymptotic (Or.inl one_ne_zero)
  simpa using hWithin

open MathlibExt.Biology.StatisticalGenetics.Kinship (Pedigree)

-- Numbering generation one in reverse order exercises the symmetry of the sibling argument.
private def samplePedigree : Pedigree 6 where
  parents i := if i.val < 2 then none else if i.val < 4 then some ![0, 1] else some ![3, 2]
  parents_lt i p hi j := by
    split at hi
    · contradiction
    · rename_i hi₂
      split at hi
      · cases hi
        fin_cases j
        · change 0 < i.val; omega
        · change 1 < i.val; omega
      · cases hi
        fin_cases j
        · change 3 < i.val; omega
        · change 2 < i.val; omega

private def samplePair : ℕ → Fin 2 → Fin 6
  | 0 => ![0, 1]
  | 1 => ![3, 2]
  | _ + 2 => ![4, 5]

example : (∀ a, 1 - samplePedigree.inbreeding (samplePair 2 a) = 3 / 4) ∧
    1 - samplePedigree.geneDropKinship (samplePair 2 0) (samplePair 2 1) = 5 / 8 := by
  have founders (a : Fin 2) : samplePedigree.parents (samplePair 0 a) = none := by
    fin_cases a <;> rfl
  have distinct (t : ℕ) (ht : t ≤ 2) : samplePair t 0 ≠ samplePair t 1 := by
    interval_cases t <;> decide
  have parents (t : ℕ) (ht : t < 2) (a : Fin 2) :
      samplePedigree.parents (samplePair (t + 1) a) = some (samplePair t) := by
    interval_cases t <;> fin_cases a <;> rfl
  have h := pedigree_nonIdentity samplePedigree samplePair founders distinct parents 2 le_rfl
  have hValues : nonIdentity 1 1 2 = (3 / 4, 5 / 8) := by norm_num [nonIdentity]
  rw [hValues] at h
  exact h

end Domains.Biology.PopulationGenetics.Classical.FullSibMating
