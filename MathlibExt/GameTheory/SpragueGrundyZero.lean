/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SpragueGrundy

/-!
# P-positions and Sprague–Grundy value zero

An impartial game equivalent to a Nim heap starts at a P-position exactly when the heap is empty.
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace isP_start_iff_of_equiv_nimHeap

private theorem isP_sum_zero_iff (G : ImpartialGame) (p : G.Pos) :
    IsP (gameSum G (nimHeap 0)) (p, (nimHeap 0).start) ↔ IsP G p := by
  let := (gameSum G (nimHeap 0)).eqDec
  induction p using (wfRel G).induction with
  | h p ih =>
    refine (isP_iff _ _).trans (Iff.trans ?_ (isP_iff G p).symm)
    constructor
    · intro h q hq
      apply mt (ih q hq).mpr
      exact h (q, (nimHeap 0).start)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
    · intro h q hq
      rcases Finset.mem_union.mp hq with hleft | hright
      · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hleft
        exact mt (ih q' hq').mp (h q' hq')
      · obtain ⟨j, hj, _⟩ := Finset.mem_image.mp hright
        exact (Nat.not_lt_zero _ (Finset.mem_filter.mp hj).2).elim

private theorem isP_nimHeap_start_iff (n : ℕ) : IsP (nimHeap n) (nimHeap n).start ↔ n = 0 := by
  have hzero (m : ℕ) : IsP (nimHeap m) (0 : Fin (m + 1)) :=
    (isP_iff _ _).mpr fun _ hq => (Nat.not_lt_zero _ (Finset.mem_filter.mp hq).2).elim
  constructor
  · intro h
    by_contra hn
    have hmove : (0 : Fin (n + 1)) ∈ (nimHeap n).moves (nimHeap n).start :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ (0 : Fin (n + 1)), Nat.pos_of_ne_zero hn⟩
    exact (isP_iff _ _).mp h _ hmove (hzero n)
  · rintro rfl
    exact hzero 0

end isP_start_iff_of_equiv_nimHeap

open isP_start_iff_of_equiv_nimHeap in
/-- **P-positions are the games of Sprague–Grundy value zero.** Let $G$ be a finite impartial game
and $n$ a natural number such that $G$ is equivalent to the Nim heap $*n$, that is, $G$ has
Sprague–Grundy value $n$. Then the starting position of $G$ is a P-position if and only if
$n = 0$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 6 (`integers-2026-G4-thm-6`). -/
public theorem isP_start_iff_of_equiv_nimHeap (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    IsP G G.start ↔ n = 0 := by
  calc
    IsP G G.start ↔ IsP (gameSum G (nimHeap 0)) (G.start, (nimHeap 0).start) :=
      (isP_sum_zero_iff _ _).symm
    _ ↔ IsP (gameSum (nimHeap n) (nimHeap 0)) ((nimHeap n).start, (nimHeap 0).start) :=
      hG (nimHeap 0)
    _ ↔ IsP (nimHeap n) (nimHeap n).start := isP_sum_zero_iff _ _
    _ ↔ n = 0 := isP_nimHeap_start_iff n

end MetaMathlibExt
