/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.FinCases
import MathlibExt.GroupTheory.BrauerFowler

/-! # Brauer–Fowler theorem on the alternating group of degree five -/

namespace MathlibExtTest.GroupTheory.BrauerFowler

open Equiv Equiv.Perm
open MathlibExt.GroupTheory.BrauerFowlerWanted.GroupTheory

private abbrev A5 := alternatingGroup (Fin 5)

private def doubleSwap : A5 :=
  ⟨swap 0 1 * swap 2 3,
    mul_mem_alternatingGroup_of_isSwap
      (swap_isSwap_iff.mpr (by decide)) (swap_isSwap_iff.mpr (by decide))⟩

private def threeCycle : A5 :=
  ⟨swap 0 1 * swap 0 4,
    mul_mem_alternatingGroup_of_isSwap
      (swap_isSwap_iff.mpr (by decide)) (swap_isSwap_iff.mpr (by decide))⟩

example : ∃ f : ℕ → ℕ,
    60 ≤ f (Nat.card (Subgroup.centralizer ({doubleSwap} : Set A5))) := by
  have hs : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have ht : orderOf doubleSwap = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      fin_cases i <;> rfl
    · intro h
      have heq := congrArg (fun g : A5 => g.val (0 : Fin 5)) h
      exact (by decide : (1 : Fin 5) ≠ 0) heq
  have hnoncomm : ∃ a b : A5, a * b ≠ b * a := by
    refine ⟨doubleSwap, threeCycle, fun h => ?_⟩
    have heq := congrArg (fun g : A5 => g.val (0 : Fin 5)) h
    exact (by decide : (4 : Fin 5) ≠ 0) heq
  have hcard : Nat.card A5 = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  obtain ⟨f, hf⟩ := brauer_fowler
  rw [← hcard]
  exact ⟨f, hf A5 hs hnoncomm doubleSwap ht⟩

end MathlibExtTest.GroupTheory.BrauerFowler
