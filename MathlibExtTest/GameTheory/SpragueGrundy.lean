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

-- Mex rule: the one-token heap has only one move, so that option must have value zero.
example : Equiv { nimHeap 1 with start := (0 : Fin 2) } (nimHeap 0) := by
  obtain ⟨q, hq, he⟩ :=
    (spragueGrundyValue_eq_mex_options (nimHeap 1) 1 (fun _ => Iff.rfl)).2 0 Nat.zero_lt_one
  have hlt : q.val < 1 := (Finset.mem_filter.mp hq).2
  have hzero : q = (0 : Fin 2) := Fin.ext (Nat.lt_one_iff.mp hlt)
  simpa only [hzero] using he

-- Mex rule: a zero-valued position can still have moves, and every such move has positive value.
example (G : ImpartialGame) (hG : Equiv G (nimHeap 0)) (q : G.Pos) (hq : q ∈ G.moves G.start) :
    ∃ n > 0, Equiv { G with start := q } (nimHeap n) := by
  obtain ⟨n, hn⟩ := sprague_grundy { G with start := q }
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  rintro rfl
  exact (spragueGrundyValue_eq_mex_options G 0 hG).1 q hq hn

end MetaMathlibExt.SpragueGrundy
