/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SpragueGrundyMex

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- The one-token heap has only one move, so that particular option must have value zero.
example : Equiv { nimHeap 1 with start := (0 : Fin 2) } (nimHeap 0) := by
  obtain ⟨q, hq, he⟩ :=
    (spragueGrundyValue_eq_mex_options (nimHeap 1) 1 (fun _ => Iff.rfl)).2 0 Nat.zero_lt_one
  have hlt : q.val < 1 := (Finset.mem_filter.mp hq).2
  have hzero : q = (0 : Fin 2) := Fin.ext (Nat.lt_one_iff.mp hlt)
  simpa only [hzero] using he

-- A zero-valued position can still have moves. Every such move has positive value.
example (G : ImpartialGame) (hG : Equiv G (nimHeap 0)) (q : G.Pos) (hq : q ∈ G.moves G.start) :
    ∃ n > 0, Equiv { G with start := q } (nimHeap n) := by
  obtain ⟨n, hn⟩ := sprague_grundy { G with start := q }
  refine ⟨n, Nat.pos_of_ne_zero ?_, hn⟩
  rintro rfl
  exact (spragueGrundyValue_eq_mex_options G 0 hG).1 q hq hn
