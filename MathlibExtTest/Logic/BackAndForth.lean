/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.BackAndForth

/-!
# Tests for Ehrenfeucht–Fraïssé games on finite binary relations

* The empty position is a partial isomorphism, so Duplicator wins every zero-round game from it.
* Empty versus nonempty domain: Spoiler picks the point of the one-point structure and Duplicator
  has no answer, so Duplicator loses the one-round game.
* A loop versus no loop on one point: Duplicator wins one round between two loops and loses one
  round between a loop and a loopless point. `DuplicatorWin.symm` transfers the loss to the game
  with the two structures swapped.
* An edge versus no edge on two points: Duplicator wins one round, since neither structure has a
  loop, but loses two rounds, since Spoiler can play both endpoints of the edge; a win in `k`
  rounds does not give a win in `k + 1` rounds. Between two copies of the edge Duplicator wins
  two rounds, and `DuplicatorWin.mono` turns that into a one-round win.
-/

@[expose] public section

namespace MathlibExt.Logic.BackAndForth.Tests

/-- The empty relation on `Fin n`. -/
def emptyRel (n : ℕ) : Fin n → Fin n → Bool := fun _ _ => false

/-- One point with a loop. -/
def loop : Fin 1 → Fin 1 → Bool := fun _ _ => true

/-- Two points with a single edge, from `0` to `1`. -/
def edge : Fin 2 → Fin 2 → Bool := fun a b => decide (a = 0 ∧ b = 1)

/-- The empty position is a partial isomorphism, so Duplicator wins the zero-round game from it
between any two relations. -/
example {n m : ℕ} (R : Fin n → Fin n → Bool) (S : Fin m → Fin m → Bool) :
    DuplicatorWin R S 0 [] := by
  constructor <;> intro p hp <;> simp at hp

/-- Empty versus one point: Spoiler picks the point and Duplicator has no answer. -/
example : ¬ DuplicatorWin (emptyRel 0) (emptyRel 1) 1 [] := by
  rintro ⟨-, h⟩
  obtain ⟨a, -⟩ := h 0
  exact a.elim0

/-- Two loops: Duplicator wins one round. -/
example : DuplicatorWin loop loop 1 [] := by
  simp only [DuplicatorWin, PartialIso]
  decide

/-- A loop versus a loopless point: Duplicator loses one round. -/
theorem not_duplicatorWin_loop_emptyRel : ¬ DuplicatorWin loop (emptyRel 1) 1 [] := by
  simp only [DuplicatorWin, PartialIso]
  decide

/-- `DuplicatorWin.symm` transfers the loss to the game with the structures swapped. -/
example : ¬ DuplicatorWin (emptyRel 1) loop 1 [] := fun h =>
  not_duplicatorWin_loop_emptyRel (DuplicatorWin.symm _ _ h)

/-- An edge versus no edge: Duplicator wins one round, since neither structure has a loop. -/
example : DuplicatorWin edge (emptyRel 2) 1 [] := by
  simp only [DuplicatorWin, PartialIso]
  decide

/-- An edge versus no edge: Duplicator loses two rounds, since Spoiler can play both endpoints of
the edge. -/
example : ¬ DuplicatorWin edge (emptyRel 2) 2 [] := by
  simp only [DuplicatorWin, PartialIso]
  decide

/-- Two copies of the edge: Duplicator wins two rounds by copying Spoiler's moves. -/
theorem duplicatorWin_edge_edge : DuplicatorWin edge edge 2 [] := by
  simp only [DuplicatorWin, PartialIso]
  decide

/-- `DuplicatorWin.mono` turns the two-round win into a one-round win. -/
example : DuplicatorWin edge edge 1 [] :=
  DuplicatorWin.mono _ _ duplicatorWin_edge_edge

end MathlibExt.Logic.BackAndForth.Tests
