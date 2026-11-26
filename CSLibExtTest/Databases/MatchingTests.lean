/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.Matching
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Tests for matching databases -/

open Cslib.Databases.Matching Cslib.Probability.PMF
open scoped ENNReal

-- The cycle and its inverse differ at 0. Both column order and permutation direction matter.
private def cycles : Fin 2 → Equiv.Perm (Fin 3) := ![finRotate 3, (finRotate 3).symm]

example : ![(0 : Fin 3), 1, 2] ∈ ((permutationEquiv 3 2) cycles).1 := by
  rw [mem_permutationEquiv_iff]
  decide

example : ![(0 : Fin 3), 2, 1] ∉ ((permutationEquiv 3 2) cycles).1 := by
  rw [mem_permutationEquiv_iff]
  decide

example : Fintype.card (MatchingRelation 3 2) = 36 := by rw [card_matchingRelation]; decide

-- The only unary relation is the full domain, for every n > 0.
example (n : ℕ) [NeZero n] (R : MatchingRelation n 0) : R.1 = Finset.univ := by
  obtain ⟨σ, rfl⟩ := (permutationEquiv n 0).surjective R
  apply Finset.eq_univ_of_forall
  intro t
  exact (mem_permutationEquiv_iff σ t).2 (fun j => j.elim0)

example (k : ℕ) : Fintype.card (MatchingRelation 1 k) = 1 := by simp [card_matchingRelation]

-- Listing the same tuple twice does not supply two rows of a matching.
example (t : Fin 2 → Fin 2) : ¬ IsMatching [t, t].toFinset := by
  intro h
  simpa using h.card_eq

-- The full binary relation covers every value at both columns, but repeats column values.
example : let R := (Finset.univ : Finset (Fin 2 → Fin 2))
    (∀ c, Function.Surjective fun t : R => t.1 c) ∧ ¬ IsMatching R := by
  dsimp only
  constructor
  · exact fun _ x => ⟨⟨fun _ => x, Finset.mem_univ _⟩, rfl⟩
  · intro h
    have hc := h.card_eq
    simp at hc

-- Binary and ternary relations on three values: three independent permutations, not one.
example (D : MatchingDatabase 3 (fun b : Bool => if b then 2 else 1)) :
    (independentPermutations 3 _ |>.map (databaseEquiv 3 _)) D = (216 : ℝ≥0∞)⁻¹ := by
  rw [map_independentPermutations, uniform_matchingDatabase_apply]
  congr 2

-- No relation names: no permutation draws and exactly one database of probability one.
example (D : MatchingDatabase 3 (fun i : Fin 0 => i.elim0)) :
    uniformOfFintype _ D = 1 := by
  rw [uniform_matchingDatabase_apply]
  simp

-- Correlating two columns by reusing one permutation misses the off-diagonal family.
example : cycles ∉ ((uniformOfFintype (Equiv.Perm (Fin 3))).map
    (fun s => fun _ : Fin 2 => s)).support := by
  intro h
  rw [PMF.support_map] at h
  obtain ⟨s, -, hs⟩ := h
  have h0 := congrArg (fun f : Fin 2 → Equiv.Perm (Fin 3) => f 0 0) hs
  have h1 := congrArg (fun f : Fin 2 → Equiv.Perm (Fin 3) => f 1 0) hs
  exact (by decide : cycles 0 0 ≠ cycles 1 0) (h0.symm.trans h1)
