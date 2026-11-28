/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DodgsonScoreDefs
import CSLibExt.Complexity.NPComplete.EvolominoDefs
import CSLibExt.Complexity.NPComplete.HornCoreDefs

/-!
# Boundary behavior of three helper predicates

`DodgsonScore.IsCondorcetWinner`, `Evolomino.Linked` and `HornCore.IsHornModelSet` hold in cases
outside the range their decision languages use: an out-of-range candidate, a square outside the
set, and members of the wrong length. These tests pin those cases down.
-/

namespace MetaMathlibExt.Complexity.NPComplete

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)

section DodgsonScore

open DodgsonScore

/-- For an out-of-range candidate `c ≥ m`, being a Condorcet winner only asks that the lists be
the orders of a profile. -/
private theorem DodgsonScore.isCondorcetWinner_of_le {m c : ℕ} {V : List (List ℕ)}
    (h : m ≤ c) :
    IsCondorcetWinner m V c ↔ ∃ R : Profile (Fin m) (Fin V.length),
      ∀ v a b, (R v).lt a b ↔ (V.get v).idxOf a.1 < (V.get v).idxOf b.1 := by
  constructor
  · rintro ⟨R, hR, -⟩
    exact ⟨R, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, hR, fun a _ ha _ => absurd ha (by omega)⟩

/-- The order of `Fin 1`, which has no strict comparisons. -/
private def fin1Order : MathlibExt.Order.StrictTotalOrder (Fin 1) where
  lt a b := a.1 < b.1
  irrefl _ := Nat.lt_irrefl _
  trans := Nat.lt_trans
  total {a b} h := absurd (Subsingleton.elim a b) h

/-- `5` is not one of the candidates `0`, yet it counts as a Condorcet winner of `[[0]]`. -/
example : IsCondorcetWinner 1 [[0]] 5 := by
  refine (DodgsonScore.isCondorcetWinner_of_le (by decide)).2
    ⟨fun _ => fin1Order, fun v a b => ?_⟩
  change a.1 < b.1 ↔ _
  revert v a b
  decide

end DodgsonScore

section Evolomino

open Evolomino

/-- Every square is linked to itself, even outside `S`. -/
private theorem Evolomino.linked_refl (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Linked S p p :=
  Relation.ReflTransGen.refl

/-- A square outside `S` is linked only to itself. -/
private theorem Evolomino.linked_iff_eq_of_not_mem {S : Finset (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hp : p ∉ S) :
    Linked S p q ↔ q = p := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨_, ⟨hp', -⟩, -⟩
    · exact h.symm
    · exact absurd hp' hp
  · rintro rfl
    exact linked_refl S _

/-- A square outside `S` is linked to no other square. -/
private theorem Evolomino.not_linked_of_not_mem {S : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (hq : q ∉ S)
    (hpq : p ≠ q) : ¬ Linked S p q := by
  intro h
  rcases h.cases_tail with h | ⟨_, -, ⟨-, hq', -⟩⟩
  · exact hpq h.symm
  · exact hq hq'

/-- The empty set has no blocks, yet `(0, 0)` is linked to itself in it. -/
example : Linked ∅ (0, 0) (0, 0) := linked_refl ∅ (0, 0)

/-- Two adjacent squares of `S` are linked. -/
example : Linked {(0, 0), (0, 1)} (0, 0) (0, 1) :=
  Relation.ReflTransGen.single ⟨by simp, by simp, Or.inl ⟨rfl, Or.inl rfl⟩⟩

/-- A square of `S` is not linked to a square outside it. -/
example : ¬ Linked {(0, 0)} (0, 0) (0, 1) :=
  not_linked_of_not_mem (by simp) (by simp)

end Evolomino

section HornCore

open HornCore Cslib.Logic.LegacyPL

/-- Only the members of `M'` of length `n` matter. -/
private theorem HornCore.isHornModelSet_iff_filter (n : ℕ) (M' : List (List Bool)) (φ : CNF) :
    IsHornModelSet n M' φ ↔ IsHornModelSet n (M'.filter (·.length = n)) φ := by
  unfold IsHornModelSet
  simp [List.mem_filter, List.length_ofFn]

/-- The empty formula is a Horn formula whose models on no variables are `[[], [true]]`, though
`[true]` is not an assignment to zero variables. -/
example : IsHornModelSet 0 [[], [true]] [] := by
  refine ⟨by decide, by simp, fun a => ?_⟩
  simp [CNF.Satisfies]

/-- No assignment to zero variables is the list `[true]`. -/
example (a : Fin 0 → Bool) : List.ofFn a ≠ [true] := by simp

/-- After dropping members of the wrong length, the model set of the empty formula on zero
variables is exactly `[[]]`. -/
example : IsHornModelSet 0 [[]] [] := by
  refine ⟨by decide, by simp, fun a => ?_⟩
  simp [CNF.Satisfies]

end HornCore

end MetaMathlibExt.Complexity.NPComplete
