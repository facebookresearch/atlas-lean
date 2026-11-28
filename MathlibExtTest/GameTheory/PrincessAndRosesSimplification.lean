/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import MathlibExt.GameTheory.PrincessAndRosesSimplification

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- Shifting the empty board leaves no legal simplified move, for any shift.
example (n : ℕ) : simplifiedPrincessRosesMoves (n, n, n, 0) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b, c, d⟩ h
  obtain ⟨ha, hb, hc, hd, hba, hcb, _, hm⟩ := mem_simplifiedPrincessRosesMoves.mp h
  have hmask : ∀ m ∈ simplifiedPrincessRosesMoveList,
      m.2.2.2 = 0 → m.2.2.1 = 0 ∧ (m.1 = 1 ∨ m.2.1 = 1) := by decide
  have hzero : 0 - d = 0 := Nat.zero_sub d
  have := hmask _ hm hzero
  change n - c = 0 ∧ (n - a = 1 ∨ n - b = 1) at this
  omega

-- The next player wins from (1, 0, 0, 0) in ordinary play by clearing the only nonempty pile.
example : ¬ IsP (princessRoses ![1, 0, 0, 0]) ![1, 0, 0, 0] := by
  let G := princessRoses ![1, 0, 0, 0]
  have hterminal : IsP G ![0, 0, 0, 0] := by
    refine (isP_iff G _).mpr ?_
    intro q hq
    have hlt := (mem_princessRoses_moves_iff.mp hq).2.1
    simp [Fin.sum_univ_succ] at hlt
  have hmove : ![0, 0, 0, 0] ∈ G.moves ![1, 0, 0, 0] :=
    mem_princessRoses_moves_iff.mpr (by decide)
  exact fun hP => (isP_iff G _).mp hP _ hmove hterminal

-- Its shifted simplified counterpart wins by the unique move to (1, 1, 1, 0).
example : ¬ IsP (simplifiedPrincessRoses (2, 1, 1, 0)) (2, 1, 1, 0) := by
  let G := simplifiedPrincessRoses (2, 1, 1, 0)
  let p : G.Pos := (2, 1, 1, 0)
  let q : G.Pos := (1, 1, 1, 0)
  have hoptions : G.moves p = {q} :=
    @of_decide_eq_true _ (@Finset.decidableEq G.Pos G.eqDec (G.moves p) {q}) rfl
  have hempty : G.moves q = ∅ :=
    @of_decide_eq_true _ (@Finset.decidableEq G.Pos G.eqDec (G.moves q) ∅) rfl
  have hterminal : IsP G q := by
    refine (isP_iff G q).mpr ?_
    intro r hr
    rw [hempty] at hr
    exact (Finset.notMem_empty r hr).elim
  have hmove : q ∈ G.moves p := by
    rw [hoptions]
    exact Finset.mem_singleton_self q
  exact fun hP => (isP_iff G p).mp hP q hmove hterminal

-- Even with four distinct piles, the ordinary game has moves the simplified game forbids.
example : ![4, 3, 1, 1] ∈ (princessRoses ![4, 3, 2, 1]).moves ![4, 3, 2, 1] := by
  apply mem_princessRoses_moves_iff.mpr
  decide

example : (4, 3, 1, 1) ∉ simplifiedPrincessRosesMoves (4, 3, 2, 1) := by
  decide

-- The simplified game permits taking from the third and fourth piles together.
example : (4, 3, 1, 0) ∈ simplifiedPrincessRosesMoves (4, 3, 2, 1) := by
  decide
