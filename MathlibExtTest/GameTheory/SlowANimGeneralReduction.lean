/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANimGeneralReduction

namespace MetaMathlibExt.slowANim_generalReduction

private abbrev sizes : Finset ℕ := {2, 3}
private abbrev start : Fin 3 → ℕ := ![2, 1, 1]
private abbrev tied : Fin 3 → ℕ := ![1, 1, 1]
private abbrev remainder : Fin 3 → ℕ := ![1, 0, 0]

private theorem reduced_of_reaches_zero {p : Fin 3 → ℕ}
    (h : Relation.ReflTransGen (fun x y => y ∈ slowANimMoves sizes x) p (fun _ => 0)) :
    SlowANimReduced sizes p :=
  fun _ => ⟨_, h, slowANimMoves_zero _, rfl⟩

private theorem terminal_not_reduced : ¬ SlowANimReduced sizes remainder := by
  intro h
  obtain ⟨t, ht, -, hzero⟩ := h 0
  rcases ht.cases_head with ht | ⟨q, hq, _⟩
  · subst t
    exact (by decide : remainder 0 ≠ 0) hzero
  · have hterminal : slowANimMoves sizes remainder = ∅ := by decide
    simp [hterminal] at hq

-- Playing on all three stacks hits the unique tallest stack. The surplus is zero.
example : (∑ i, start i) < 2 * Finset.univ.sup start + (3 - 2) := by
  have hstep : (![1, 0, 1] : Fin 3 → ℕ) ∈ slowANimMoves sizes start := by decide
  have hfinish : (fun _ => 0) ∈ slowANimMoves sizes ![1, 0, 1] := by decide
  have hp := reduced_of_reaches_zero ((Relation.ReflTransGen.single hfinish).head hstep)
  have hmove : slowANimAfter start Finset.univ = remainder := by decide
  rcases slowANim_generalReduction 3 sizes (by decide) (by decide) start hp
      Finset.univ (by decide) (by decide) (hmove ▸ terminal_not_reduced) with
    h | ⟨⟨i, -, hi⟩, -⟩
  · exact h.2.2.2
  · exact (hi (Finset.mem_univ i)).elim

-- Playing on two of three tied tallest stacks leaves the surplus one below the bound.
example : (∑ i, tied i) < 2 * Finset.univ.sup tied + 2 := by
  have hfinish : (fun _ => 0) ∈ slowANimMoves sizes tied := by decide
  have hp := reduced_of_reaches_zero (Relation.ReflTransGen.single hfinish)
  have hmove : slowANimAfter tied {1, 2} = remainder := by decide
  rcases slowANim_generalReduction 3 sizes (by decide) (by decide) tied hp
      {1, 2} (by decide) (by decide) (hmove ▸ terminal_not_reduced) with h | h
  · exact ((by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))) (h.2.1 0 (by decide))).elim
  · exact h.2.2

end MetaMathlibExt.slowANim_generalReduction
