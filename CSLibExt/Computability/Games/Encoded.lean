/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Encoded finite parity games
-/
module

public import CSLibExt.Computability.Games.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Encoded finite parity games

A parity game on `Fin n` whose data are *decidable*: the owner is a `Bool`
(`false` for the even player, `true` for the odd player), the move relation
is a `Bool`-valued matrix, and the priority is a function to `ℕ`. The
`ParityGame` API (`CSLibExt.Computability.Games.Parity`) takes the move
relation as an arbitrary `Prop`, so it cannot be executed or counted; the
encoded form is the one algorithms and verifiers run on. There is deliberately
no seriality field: restricted subgames (used by Zielonka's recursion) need
not be serial on the whole arena, only on the live set.

Main definitions:

* `Cslib.Games.EncodedParityGame`: the encoded game.
* `Cslib.Games.EncodedParityGame.toParityGame`: the `ParityGame` of a serial
  encoded game.
* `Cslib.Games.EncodedParityGame.dualGame`: the dual game, owners swapped
  and priorities incremented by one, whose even winning region is the
  original game's odd winning region.
* `Cslib.Games.EncodedParityGame.cpreIn`, `Cslib.Games.EncodedParityGame.attractorIn`:
  the controllable predecessor and the attractor *inside* a live set `U`
  (attractors of Zielonka's recursion).
* `Cslib.Games.EncodedParityGame.maxPriorityIn`,
  `Cslib.Games.EncodedParityGame.maxPositionsIn`: the maximal priority on a
  live set and the positions attaining it.
* `Cslib.Games.EncodedParityGame.priorityRank`,
  `Cslib.Games.EncodedParityGame.priorityCompress`: priority compression:
  replace each priority by its rank (starting at `0`) among the distinct
  priorities actually occurring on `Fin n`, plus one if the rank should be
  odd when the priority is even (and vice versa) so as to preserve parity.
  Concretely, `priorityCompress G` is the game with the same owners and
  moves and with priority `2` times the number of distinct smaller
  priorities plus the parity of the original priority; it has distinct
  priorities exactly the even/odd pairs for the first `m` ranks, hence
  every priority at most `2 * m - 1 ≤ 2 * n - 1`, and it preserves the
  order and the parity of every pair of priorities. A play has the same
  winner (same parity of the maximal recurring priority) in the compressed
  game as in the original.

## References

* W. Zielonka, "Infinite games on finitely coloured graphs with applications to
  automata on infinite trees", *Theoretical Computer Science* 200 (1998),
  135-183 (attractors, subgames, the recursive solver).
* M. Jurdziński, "Small progress measures for solving parity games",
  *Proceedings of STACS 2000*, LNCS 1770, 290-301 (progress measures).
-/

@[expose] public section

namespace Cslib.Games

/-- An encoded finite parity game on `Fin n`: the owner as a `Bool` (`false`
for even, `true` for odd), the move relation as a `Bool`-valued matrix, and
the priority as a function to `ℕ`. No seriality is assumed: restricted
subgames need not be serial on the whole arena. -/
structure EncodedParityGame (n : ℕ) where
  /-- The owner of each position: `false` for even, `true` for odd. -/
  owner : Fin n → Bool
  /-- The move matrix: `move v w = true` iff there is a move from `v` to `w`. -/
  move : Fin n → Fin n → Bool
  /-- The priority of each position. -/
  priority : Fin n → ℕ

namespace EncodedParityGame

variable {n : ℕ} (G : EncodedParityGame n)

/-- The `ParityGame` of a serial encoded game. -/
def toParityGame (hser : ∀ v, ∃ w, G.move v w = true) : ParityGame (Fin n) where
  owner v := if G.owner v then Player.odd else Player.even
  Move v w := G.move v w = true
  priority := G.priority
  serial v := by
    obtain ⟨w, hw⟩ := hser v
    exact ⟨w, hw⟩

/-- The dual game: owners swapped and priorities incremented by one. The
even player wins the dual game exactly where the odd player wins the
original, since incrementing priorities flips every parity. -/
def dualGame : EncodedParityGame n where
  owner v := !G.owner v
  move := G.move
  priority v := G.priority v + 1

/-- The controllable predecessor inside a live set `U`: the positions of `U`
from which `p` can force the play into `X` in one move (with moves leaving
`U` ignored). -/
def cpreIn (p : Bool) (U X : Finset (Fin n)) : Finset (Fin n) :=
  U.filter fun v =>
    (if G.owner v = p then
      (List.finRange n).any fun w =>
        decide (w ∈ U) && G.move v w && decide (w ∈ X)
    else
      (List.finRange n).all fun w =>
        (!decide (w ∈ U)) || (!G.move v w) || decide (w ∈ X)) = true

/-- The attractor of `T` for `p` inside the live set `U`: `n` iterations of
`X ↦ (T ∩ U) ∪ cpreIn p U X` from `∅`. -/
def attractorIn (p : Bool) (T U : Finset (Fin n)) : Finset (Fin n) :=
  (fun X => (T ∩ U) ∪ cpreIn G p U X)^[n] ∅

/-- The rank of a priority `p` among the distinct priorities occurring in
the game: the number of distinct priorities `q < p` that occur. -/
def priorityRank (p : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).image G.priority).filter (· < p) |>.card

/-- The compressed priority of `p`: twice its rank, plus its parity.
Distinct priorities keep distinct compressed values, order is preserved,
and parity is preserved (both are `p % 2`). -/
def priorityCompressed (p : ℕ) : ℕ :=
  2 * G.priorityRank p + (p % 2)

/-- Priority compression: the game with the same owners and moves and
priorities replaced by their compressed values. Every priority is at most
`2 * n - 1` and strictly below `2 * n`, since at most `n` distinct
priorities occur. -/
def priorityCompress : EncodedParityGame n where
  owner := G.owner
  move := G.move
  priority v := G.priorityCompressed (G.priority v)

/-- The rank of an occurring priority is strictly below the number of
distinct priorities occurring: the filter defining the rank is a proper
subset of the image, since the priority itself is in the image but not in
its own strict filter. Source: M. Jurdziński, "Small progress measures for
solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem priorityRank_lt_card {v : Fin n} :
    G.priorityRank (G.priority v) <
      ((Finset.univ : Finset (Fin n)).image G.priority).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro hEq
  have hmem : G.priority v ∈ (Finset.univ : Finset (Fin n)).image G.priority :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hmemF : G.priority v ∈
      ((Finset.univ : Finset (Fin n)).image G.priority).filter
        (· < G.priority v) := by
    rw [hEq]
    exact hmem
  exact lt_irrefl _ (Finset.mem_filter.mp hmemF).2

/-- Ranks are strictly monotone in the priority: if `w` has a strictly
smaller priority than `v`, the filter for `w` is a proper subset of the
filter for `v`, since `G.priority w` is in the latter but not the former.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem priorityRank_lt_of_lt {v w : Fin n} (h : G.priority w < G.priority v) :
    G.priorityRank (G.priority w) < G.priorityRank (G.priority v) := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (Nat.le_of_lt h)⟩
  · intro hEq
    have hmem : G.priority w ∈
        ((Finset.univ : Finset (Fin n)).image G.priority).filter
          (· < G.priority v) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩, h⟩
    have hmemW : G.priority w ∈
        ((Finset.univ : Finset (Fin n)).image G.priority).filter
          (· < G.priority w) := by
      rw [hEq]
      exact hmem
    exact lt_irrefl _ (Finset.mem_filter.mp hmemW).2

/-- Ranks are monotone in the priority. Source: M. Jurdziński, "Small
progress measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
theorem priorityRank_le_of_le {v w : Fin n} (h : G.priority w ≤ G.priority v) :
    G.priorityRank (G.priority w) ≤ G.priorityRank (G.priority v) := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- Compressed priorities are bounded by `2 * n`: the number of distinct
priorities occurring is at most `n`. -/
theorem priorityCompressed_lt {v : Fin n} :
    (G.priorityCompress).priority v < 2 * n := by
  have hcard : ((Finset.univ : Finset (Fin n)).image G.priority).card ≤ n := by
    calc ((Finset.univ : Finset (Fin n)).image G.priority).card
        ≤ Finset.univ.card := Finset.card_image_le
      _ = n := by simp
  have hrank : G.priorityRank (G.priority v) < n :=
    lt_of_lt_of_le (G.priorityRank_lt_card (v := v)) hcard
  have hlt : G.priority v % 2 < 2 := Nat.mod_lt _ (by omega)
  change 2 * G.priorityRank (G.priority v) + G.priority v % 2 < 2 * n
  omega

/-- Priority compression preserves the order of priorities. -/
theorem priorityCompressed_lt_iff {v w : Fin n} :
    (G.priorityCompress).priority v < (G.priorityCompress).priority w ↔
      G.priority v < G.priority w := by
  have hmod : ∀ a, (a : ℕ) % 2 < 2 := fun a => Nat.mod_lt a (by omega)
  constructor
  · intro hlt
    by_contra hge
    have hge' : G.priority w ≤ G.priority v := Nat.le_of_not_lt hge
    by_cases heq : G.priority v = G.priority w
    · simp only [priorityCompress, priorityCompressed, heq] at hlt
      exact absurd hlt (lt_irrefl _)
    · have hlt' : G.priority w < G.priority v := lt_of_le_of_ne hge' (Ne.symm heq)
      have hstrict : G.priorityRank (G.priority w) <
          G.priorityRank (G.priority v) := G.priorityRank_lt_of_lt hlt'
      have hcomp : 2 * G.priorityRank (G.priority w) + G.priority w % 2 <
          2 * G.priorityRank (G.priority v) + G.priority v % 2 := by omega
      simp only [priorityCompress, priorityCompressed] at hlt
      omega
  · intro hlt
    have hstrict : G.priorityRank (G.priority v) <
        G.priorityRank (G.priority w) := G.priorityRank_lt_of_lt hlt
    change 2 * G.priorityRank (G.priority v) + G.priority v % 2 <
      2 * G.priorityRank (G.priority w) + G.priority w % 2
    omega

/-- Priority compression preserves the parity of priorities. -/
theorem priorityCompressed_mod_two {v : Fin n} :
    (G.priorityCompress).priority v % 2 = G.priority v % 2 := by
  change (2 * G.priorityRank (G.priority v) + G.priority v % 2) % 2 =
    G.priority v % 2
  have hlt : G.priority v % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- The maximal priority attained on a live set `U` (`0` if `U` is empty). -/
def maxPriorityIn (U : Finset (Fin n)) : ℕ :=
  U.sup G.priority

/-- The positions of a live set `U` attaining the maximal priority on `U`. -/
def maxPositionsIn (U : Finset (Fin n)) : Finset (Fin n) :=
  U.filter fun v => G.priority v = maxPriorityIn G U

end EncodedParityGame

end Cslib.Games
