/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

-- Terminal position: the empty heap has no moves, so it is a P-position.
example : IsP (nimHeap 0) (nimHeap 0).start :=
  (isP_iff _ _).mpr fun _ hq => absurd (Finset.mem_filter.mp hq).2 (Nat.not_lt_zero _)

-- Nonterminal position: a heap of size one moves to the empty heap, a P-position.
example : ¬ IsP (nimHeap 1) (nimHeap 1).start := by
  have h0 : IsP (nimHeap 1) (0 : Fin 2) :=
    (isP_iff _ _).mpr fun _ hq => absurd (Finset.mem_filter.mp hq).2 (Nat.not_lt_zero _)
  rw [isP_iff]
  exact fun h => h (0 : Fin 2)
    (by decide : (0 : Fin 2) ∈ Finset.univ.filter fun j : Fin 2 => j.val < 1) h0

-- The empty heap is equivalent to itself: its sum with itself has no moves.
example : Equiv (nimHeap 0) (nimHeap 0) := by
  let := (gameSum (nimHeap 0) (nimHeap 0)).eqDec
  rw [impartialGame_equiv_iff_isP_gameSum]
  refine (isP_iff _ _).mpr ?_
  intro q hq
  rcases Finset.mem_union.mp hq with hleft | hright
  · obtain ⟨a', ha', -⟩ := Finset.mem_image.mp hleft
    exact absurd (Finset.mem_filter.mp ha').2 (Nat.not_lt_zero _)
  · obtain ⟨b', hb', -⟩ := Finset.mem_image.mp hright
    exact absurd (Finset.mem_filter.mp hb').2 (Nat.not_lt_zero _)

-- Heaps of different sizes are not equivalent.
example : ¬ Equiv (nimHeap 0) (nimHeap 1) := by
  let := (gameSum (nimHeap 0) (nimHeap 1)).eqDec
  let := (nimHeap 0).eqDec
  let := (nimHeap 1).eqDec
  rw [impartialGame_equiv_iff_isP_gameSum]
  intro hP
  have hPopt : IsP (gameSum (nimHeap 0) (nimHeap 1))
      (((nimHeap 0).start, (0 : Fin 2)) :
        (gameSum (nimHeap 0) (nimHeap 1)).Pos) := by
    refine (isP_iff _ _).mpr ?_
    intro q hq
    rcases Finset.mem_union.mp hq with hleft | hright
    · obtain ⟨a', ha', -⟩ := Finset.mem_image.mp hleft
      exact absurd (Finset.mem_filter.mp ha').2 (Nat.not_lt_zero _)
    · obtain ⟨b', hb', -⟩ := Finset.mem_image.mp hright
      exact absurd (Finset.mem_filter.mp hb').2 (Nat.not_lt_zero _)
  have hmem : (((nimHeap 0).start, (0 : Fin 2)) :
        (gameSum (nimHeap 0) (nimHeap 1)).Pos) ∈
      (gameSum (nimHeap 0) (nimHeap 1)).moves
        (((nimHeap 0).start, (nimHeap 1).start) : _) := by
    change ((nimHeap 0).start, (0 : Fin 2)) ∈
      ((nimHeap 0).moves (nimHeap 0).start).image
        (fun a_1 => (a_1, (nimHeap 1).start)) ∪
        ((nimHeap 1).moves (nimHeap 1).start).image
          (fun b_1 => ((nimHeap 0).start, b_1))
    apply Finset.mem_union.mpr
    right
    refine Finset.mem_image.mpr ⟨(0 : Fin 2), ?_, rfl⟩
    exact (by decide : (0 : Fin 2) ∈ Finset.univ.filter fun j : Fin 2 => j.val < 1)
  exact (isP_iff _ _).mp hP _ hmem hPopt

-- A legal move from a heap of size two cannot retain its value.
example : ¬ Equiv { nimHeap 2 with start := (1 : Fin 3) } (nimHeap 2) :=
  (spragueGrundyValue_eq_mex_options (nimHeap 2) 2 (fun _ => Iff.rfl)).1 (1 : Fin 3) (by
    change (1 : Fin 3) ∈ Finset.univ.filter (fun j : Fin 3 => j.val < 2)
    decide)

-- Both smaller values are attained by options, but the least excluded value is two.
example : ∀ m < 2, ∃ q ∈ (nimHeap 2).moves (nimHeap 2).start,
    Equiv { nimHeap 2 with start := q } (nimHeap m) :=
  (spragueGrundyValue_eq_mex_options (nimHeap 2) 2 (fun _ => Iff.rfl)).2

end MetaMathlibExt.SpragueGrundy
