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

/-- **Encoded parity game.** An encoded finite parity game on the $n$ positions
$0, \dots, n - 1$ consists of an owner for each position, given as a Boolean (false for the even
player, true for the odd player), a move relation, given as a Boolean-valued $n \times n$
matrix, and a priority for each position, given as a natural number.

No seriality is assumed: a position may have no move, since restricted subgames need not be
serial on the whole arena. -/
structure EncodedParityGame (n : ℕ) where
  /-- The owner of each position: `false` for even, `true` for odd. -/
  owner : Fin n → Bool
  /-- The move matrix: `move v w = true` iff there is a move from `v` to `w`. -/
  move : Fin n → Fin n → Bool
  /-- The priority of each position. -/
  priority : Fin n → ℕ

namespace EncodedParityGame

variable {n : ℕ} (G : EncodedParityGame n)

/-- **The parity game of a serial encoded game.** Let $G$ be an encoded parity game on the
positions $\{0, \dots, n-1\}$ in which every position has a move to some position. The associated
parity game has the same positions, moves and priorities, and a position is owned by the odd
player if $G$ assigns it to the odd player and by the even player otherwise; every position has
a move by the hypothesis on $G$. -/
def toParityGame (hser : ∀ v, ∃ w, G.move v w = true) : ParityGame (Fin n) where
  owner v := if G.owner v then Player.odd else Player.even
  Move v w := G.move v w = true
  priority := G.priority
  serial v := by
    obtain ⟨w, hw⟩ := hser v
    exact ⟨w, hw⟩

/-- **Dual parity game.** The dual of an encoded parity game $G$ is the encoded parity game with
the same positions and moves in which every position is owned by the other player than in $G$
and has priority one more than in $G$.

Since incrementing priorities flips every parity, the even player wins the dual game exactly
where the odd player wins the original. -/
def dualGame : EncodedParityGame n where
  owner v := !G.owner v
  move := G.move
  priority v := G.priority v + 1

/-- **Controllable predecessor inside a set of positions.** Let $G$ be an encoded parity game,
$p$ a player (encoded as a Boolean: false for even, true for odd), and $U$, $X$ sets of
positions. The controllable predecessor of $X$ for $p$ inside $U$ is the set of positions
$v \in U$ such that either $v$ is owned by $p$ and some move of $G$ goes from $v$ to a position
of $U \cap X$, or $v$ is not owned by $p$ and every move of $G$ from $v$ to a position of $U$
ends in $X$.

Moves leaving $U$ are ignored; in particular a position of $U$ not owned by $p$ with no move into
$U$ belongs to the set. -/
def cpreIn (p : Bool) (U X : Finset (Fin n)) : Finset (Fin n) :=
  U.filter fun v =>
    (if G.owner v = p then
      (List.finRange n).any fun w =>
        decide (w ∈ U) && G.move v w && decide (w ∈ X)
    else
      (List.finRange n).all fun w =>
        (!decide (w ∈ U)) || (!G.move v w) || decide (w ∈ X)) = true

/-- **Attractor inside a set of positions.** Let $G$ be an encoded parity game on $n$ positions,
$p$ a player (encoded as a Boolean: false for even, true for odd), and $T$, $U$ sets of
positions. The attractor of $T$ for $p$ inside $U$ is the set obtained from $\emptyset$ by
applying $n$ times the map $X \mapsto (T \cap U) \cup \mathrm{CPre}_p^U(X)$, where
$\mathrm{CPre}_p^U(X)$ is the controllable predecessor of $X$ for $p$ inside $U$. -/
def attractorIn (p : Bool) (T U : Finset (Fin n)) : Finset (Fin n) :=
  (fun X => (T ∩ U) ∪ cpreIn G p U X)^[n] ∅

/-- The rank of a priority `p` among the distinct priorities occurring in
the game: the number of distinct priorities `q < p` that occur. -/
def priorityRank (p : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).image G.priority).filter (· < p) |>.card

/-- **Compressed priority.** Let $G$ be an encoded parity game on the positions
$\{0, \dots, n-1\}$. The compressed priority of a natural number $p$ is $2r + (p \bmod 2)$, where
$r$ is the rank of $p$ in $G$: the number of distinct priorities $q < p$ that occur in $G$.

The compressed priority of $p$ is congruent to $p$ modulo $2$. On the priorities that occur in
$G$, compression is injective and strictly increasing. -/
def priorityCompressed (p : ℕ) : ℕ :=
  2 * G.priorityRank p + (p % 2)

/-- **Priority compression.** For an encoded parity game $G$ on $n$ positions, the compressed game
has the same owners and moves as $G$ and gives each position $v$ the priority $2r + (q \bmod 2)$,
where $q$ is the priority of $v$ in $G$ and $r$ is the number of distinct priorities occurring
in $G$ that are smaller than $q$.

Since at most $n$ distinct priorities occur, every compressed priority is strictly below $2n$. -/
def priorityCompress : EncodedParityGame n where
  owner := G.owner
  move := G.move
  priority v := G.priorityCompressed (G.priority v)

/-- **Priority ranks are below the number of priorities.** Let $G$ be an encoded parity game,
and for a natural number $p$ let the rank of $p$ be the number of distinct priorities $q < p$
that occur in $G$. For every position $v$ of $G$, the rank of the priority of $v$ is strictly
less than the number of distinct priorities that occur in $G$.

The priorities below the priority of $v$ form a proper subset of the occurring priorities, since
the priority of $v$ occurs but is not below itself.

Source: M. Jurdziński, "Small progress measures for
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

/-- **Strict monotonicity of priority ranks.** Let $G$ be an encoded parity game, and for a
natural number $p$ let the rank of $p$ be the number of distinct priorities $q < p$ that occur
in $G$. If $v$ and $w$ are positions of $G$ and the priority of $w$ is strictly less than the
priority of $v$, then the rank of the priority of $w$ is strictly less than the rank of the
priority of $v$.

The priority of $w$ is counted in the rank of the priority of $v$ but not in its own rank.

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

/-- **Monotonicity of priority ranks.** Let $G$ be an encoded parity game, and for a natural
number $p$ let the rank of $p$ be the number of distinct priorities $q < p$ that occur in $G$. If
$v$ and $w$ are positions of $G$ and the priority of $w$ is at most the priority of $v$, then the
rank of the priority of $w$ is at most the rank of the priority of $v$.

Source: M. Jurdziński, "Small
progress measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
theorem priorityRank_le_of_le {v w : Fin n} (h : G.priority w ≤ G.priority v) :
    G.priorityRank (G.priority w) ≤ G.priorityRank (G.priority v) := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- **Bound on compressed priorities.** For an encoded parity game $G$ on $n$ positions, every
priority of the priority-compressed game of $G$ is strictly less than $2n$.

This holds because at most $n$ distinct priorities occur in $G$. -/
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

/-- **Priority compression preserves and reflects the order of priorities.** For an encoded
parity game $G$ and positions $v$, $w$, the priority of $v$ is smaller than the priority of $w$
in the priority-compressed game of $G$ if and only if it is smaller in $G$. -/
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

/-- **Priority compression preserves parity.** For an encoded parity game $G$ and every position
$v$, the priority of $v$ in the priority-compressed game of $G$ has the same parity as the
priority of $v$ in $G$. -/
theorem priorityCompressed_mod_two {v : Fin n} :
    (G.priorityCompress).priority v % 2 = G.priority v % 2 := by
  change (2 * G.priorityRank (G.priority v) + G.priority v % 2) % 2 =
    G.priority v % 2
  have hlt : G.priority v % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- **Maximal priority on a set of positions.** For an encoded parity game $G$ and a set $U$ of
positions, the maximal priority on $U$ is the largest priority of $G$ at a position of $U$, or
$0$ if $U$ is empty. -/
def maxPriorityIn (U : Finset (Fin n)) : ℕ :=
  U.sup G.priority

/-- **Positions of maximal priority.** For an encoded parity game $G$ and a set $U$ of positions,
the positions of maximal priority in $U$ are the positions $v \in U$ whose priority equals the
maximal priority of $G$ on $U$. -/
def maxPositionsIn (U : Finset (Fin n)) : Finset (Fin n) :=
  U.filter fun v => G.priority v = maxPriorityIn G U

end EncodedParityGame

end Cslib.Games
