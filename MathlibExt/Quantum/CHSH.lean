/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-!
# Classical CHSH bound

In the CHSH game, Alice and Bob receive bits `x, y` and
output bits; deterministic strategies win the pair `(x, y)`
when `A x XOR B y = x AND y`. At most three of the four
input pairs can win. The quantum violation is not included
here.
-/

@[expose] public section

/-- CHSH win predicate (classical core of QCI-05): Alice and
Bob output bits `A x`, `B y` on inputs `x y`; they win when
`A x XOR B y = x AND y`. -/
def chshWin (A B : Fin 2 → Bool) (x y : Fin 2) : Bool :=
  (A x != B y) == (x == 1 && y == 1)

private theorem chsh_not_all_aux (A B : Fin 2 → Bool) :
    ¬ ∀ x y : Fin 2, chshWin A B x y = true := by
  intro h
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [chshWin] at h00 h01 h10 h11
  have e00 : ((0 : Fin 2) == 1 && (0 : Fin 2) == 1) = false := by decide
  have e01 : ((0 : Fin 2) == 1 && (1 : Fin 2) == 1) = false := by decide
  have e10 : ((1 : Fin 2) == 1 && (0 : Fin 2) == 1) = false := by decide
  have e11 : ((1 : Fin 2) == 1 && (1 : Fin 2) == 1) = true := by decide
  rw [e00] at h00
  rw [e01] at h01
  rw [e10] at h10
  rw [e11] at h11
  simp at h00 h01 h10 h11
  exact h11 (h10.trans (h00.symm.trans h01))

/-- Classical CHSH bound: for any deterministic strategies,
at most 3 of the 4 input pairs win. -/
theorem chsh_le_three (A B : Fin 2 → Bool) :
    (Finset.univ.filter (fun p : Fin 2 × Fin 2 => chshWin A B p.1 p.2)).card
      ≤ 3 := by
  have hcard4 : Fintype.card (Fin 2 × Fin 2) = 4 := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have huniv : (Finset.univ : Finset (Fin 2 × Fin 2)).card = 4 := by
    rw [Finset.card_univ, hcard4]
  have hle : (Finset.univ.filter (fun p : Fin 2 × Fin 2 => chshWin A B p.1 p.2)).card ≤ 4 := by
    rw [← huniv]
    exact Finset.card_filter_le _ _
  have hne : (Finset.univ.filter (fun p : Fin 2 × Fin 2 => chshWin A B p.1 p.2)).card ≠ 4 := by
    intro h_eq4
    have h_eq_univ : Finset.univ.filter (fun p : Fin 2 × Fin 2 => chshWin A B p.1 p.2) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h_eq4, hcard4]
    have hall : ∀ x y : Fin 2, chshWin A B x y = true := by
      intro x y
      have hmem : (x, y) ∈ Finset.univ.filter (fun p : Fin 2 × Fin 2 => chshWin A B p.1 p.2) := by
        rw [h_eq_univ]
        exact Finset.mem_univ _
      rw [Finset.mem_filter] at hmem
      exact hmem.2
    exact chsh_not_all_aux A B hall
  omega

/-- In particular no deterministic strategy wins all four. -/
theorem chsh_not_all (A B : Fin 2 → Bool) :
    ¬ ∀ x y : Fin 2, chshWin A B x y = true := by
  exact chsh_not_all_aux A B

end
