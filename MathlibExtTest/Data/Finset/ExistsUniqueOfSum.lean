/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Data.Finset.ExistsUniqueOfSum
import Mathlib.Tactic.NormNum

open Finset

-- Identity transport preserves the unique selected element.
example : ∃! a : ℕ, a ∈ ({0, 1, 2} : Finset ℕ) ∧ a = 1 := by
  exact Finset.existsUnique_of_sum_comp ({0, 1, 2} : Finset ℕ)
    ({0, 1, 2} : Finset ℕ) id (fun _ => rfl) (fun a => a = 1)
      ⟨1, by simp, by simp_all⟩

-- A nontrivial reindex sends the unique target witness 20 back to source witness 1.
example :
    ∃! a : ℕ, a ∈ ({0, 1} : Finset ℕ) ∧ a = 1 := by
  let i : ℕ → ℕ := fun a => if a = 0 then 10 else 20
  have hsum : ∀ F : ℕ → ℤ,
      ∑ a ∈ ({0, 1} : Finset ℕ), F (i a) = ∑ b ∈ ({10, 20} : Finset ℕ), F b := by
    intro F
    simp [i]
  have hQ : ∃! b : ℕ, b ∈ ({10, 20} : Finset ℕ) ∧ b = 20 :=
    ⟨20, by simp, by simp_all⟩
  obtain ⟨a, ha, ha_unique⟩ :=
    Finset.existsUnique_of_sum_comp ({0, 1} : Finset ℕ) ({10, 20} : Finset ℕ) i
      hsum (fun b => b = 20) hQ
  have h1 : (1 : ℕ) ∈ ({0, 1} : Finset ℕ) ∧ i 1 = 20 := by simp [i]
  have ha1 : a = 1 := (ha_unique 1 h1).symm
  exact ⟨a, ⟨ha.1, ha1⟩, fun a' ha' => ha'.2.trans ha1.symm⟩

-- Collapsing two source points onto one target point violates the universal sum premise at F = 1.
example : ¬ ∀ F : ℕ → ℤ,
    ∑ _a ∈ ({0, 1} : Finset ℕ), F 10 = ∑ b ∈ ({10} : Finset ℕ), F b := by
  intro hsum
  have h := hsum (fun _ => 1)
  norm_num at h

#print axioms Finset.existsUnique_of_sum_comp
