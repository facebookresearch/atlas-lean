/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SpragueGrundy
import all MathlibExt.GameTheory.SpragueGrundy
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Mex rule for Sprague–Grundy values

The value of a finite impartial game is the least natural number missing from its option values.
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace spragueGrundyValue_eq_mex_options

private theorem equiv_nimHeap_iff (G : ImpartialGame) (n : ℕ) :
    Equiv G (nimHeap n) ↔ grundy G G.start = n := by
  have hn : grundy (nimHeap n) (nimHeap n).start = n := nim_grundy n _
  constructor
  · intro h
    -- Compare both games after adding a heap of size n.
    simpa [isP_sum_iff, Nat.xor_eq_zero_iff, hn] using h (nimHeap n)
  · intro h K
    simp only [isP_sum_iff, Nat.xor_eq_zero_iff, hn, h]

end spragueGrundyValue_eq_mex_options

open spragueGrundyValue_eq_mex_options in
/-- **Mex rule for Sprague–Grundy values.** Let $G$ be a finite impartial game and $n$ a natural
number such that $G$ is equivalent to the Nim heap $*n$, that is, $G$ has Sprague–Grundy value
$n$. For a move from the start position of $G$ to a position $q$, write $G_q$ for the game $G$
started at $q$. Then no $G_q$ is equivalent to $*n$, and for every natural number $m < n$ some
$G_q$ is equivalent to $*m$. That is, the Sprague–Grundy value of $G$ is the mex of the
Sprague–Grundy values of the games $G_q$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Corollary 4 (`integers-2026-G4-cor-4`). -/
public theorem spragueGrundyValue_eq_mex_options (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    (∀ q ∈ G.moves G.start, ¬ Equiv { G with start := q } (nimHeap n)) ∧
      ∀ m < n, ∃ q ∈ G.moves G.start, Equiv { G with start := q } (nimHeap m) := by
  obtain rfl := (equiv_nimHeap_iff G n).mp hG
  constructor
  · intro q hq he
    exact grundy_ne_of_mem G hq ((equiv_nimHeap_iff _ _).mp he)
  · intro m hm
    obtain ⟨q, hq, hval⟩ := exists_move_with_grundy G G.start hm
    exact ⟨q, hq, (equiv_nimHeap_iff _ _).mpr hval⟩

end MetaMathlibExt
