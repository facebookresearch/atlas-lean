/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Parity games
-/
module

public import CSLibExt.Foundations.Data.OmegaSequence.Parity

/-!
# Parity games

A parity game is played by two players, `even` and `odd`, on a directed graph of positions. Each
position belongs to one player, who chooses the next position along an edge; each position has
a natural-number priority. An infinite play is won by `even` iff the largest priority occurring
infinitely often is even (`Cslib.ωSequence.ParityEven`), and by `odd` iff it is odd. If no
priority is maximal among those occurring infinitely often (possible only with unbounded
priorities), neither player wins; `wonBy_or_wonBy_opponent` assumes bounded priorities.

This file gives the definitions and basic lemmas only:

* `Cslib.Games.ParityGame`, plays (`IsPlay`), and their winners (`WonBy`).
* `Cslib.Games.ParityGame.PositionalStrategy` (always available, `nonempty_positionalStrategy`),
  conforming plays, `WinsFrom`, and winning regions
  `WinningRegion` for positional (memoryless) strategies.
* `ParityGame.wonBy_or_wonBy_opponent`, `ParityGame.not_wonBy_and_wonBy_opponent`: with bounded
  priorities every play has exactly one winner; `ParityGame.wonBy_drop_iff`: winning is prefix
  independent.
* `ParityGame.outcome`: the unique play from a position conforming to a strategy of each player
  (`outcome_isPlay`, `outcome_conforms`, `outcome_conforms_opponent`), hence winning regions of
  the two players are disjoint (`ParityGame.disjoint_winningRegion`).
* `ParityGame.WinsFrom.of_move`: a winning strategy keeps winning after any move it allows, so
  winning regions are closed under such moves.

Positional determinacy (every position is in one of the two winning regions) is not proved here.

## References

* E. Grädel, W. Thomas, T. Wilke (eds.), *Automata, Logics, and Infinite Games*, LNCS 2500,
  Springer, 2002, Chapter 2 ("Infinite Games").
-/

@[expose] public section

namespace Cslib.Games

open Filter ωSequence

/-- The two players of a parity game. -/
inductive Player where
  /-- The player who wins plays whose maximal recurring priority is even. -/
  | even
  /-- The player who wins plays whose maximal recurring priority is odd. -/
  | odd
  deriving DecidableEq, Repr

namespace Player

/-- The other player. -/
def opponent : Player → Player
  | even => odd
  | odd => even

@[simp] theorem opponent_even : opponent even = odd := rfl

@[simp] theorem opponent_odd : opponent odd = even := rfl

@[simp] theorem opponent_opponent (p : Player) : p.opponent.opponent = p := by
  cases p <;> rfl

theorem opponent_ne (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

/-- Every player is `p` or the opponent of `p`. -/
theorem eq_or_eq_opponent (p q : Player) : q = p ∨ q = p.opponent := by
  cases p <;> cases q <;> simp

/-- The parity condition won by a player, on a sequence of priorities. -/
def Wins : Player → ωSequence ℕ → Prop
  | even, ps => ParityEven ps
  | odd, ps => ParityOdd ps

end Player

/-- A parity game on a type of positions: an owner and a priority for each position, and the
move relation. As in the usual infinite-play model, every position has a move (no dead ends), so
both players always have positional strategies (`nonempty_positionalStrategy`). -/
structure ParityGame (Pos : Type*) where
  /-- The player choosing the move at each position. -/
  owner : Pos → Player
  /-- The moves: `Move v w` iff the owner of `v` may move from `v` to `w`. -/
  Move : Pos → Pos → Prop
  /-- The priority of each position. -/
  priority : Pos → ℕ
  /-- Every position has a move. -/
  serial : ∀ v, ∃ w, Move v w

namespace ParityGame

variable {Pos : Type*} (G : ParityGame Pos)

/-- A play is an infinite sequence of positions following moves. -/
def IsPlay (π : ωSequence Pos) : Prop :=
  ∀ i, G.Move (π i) (π (i + 1))

/-- Player `p` wins the play `π`. -/
def WonBy (p : Player) (π : ωSequence Pos) : Prop :=
  p.Wins (π.map G.priority)

/-- A positional (memoryless) strategy for player `p`: a choice of successor at each position,
legal at the positions `p` owns. Its values elsewhere are irrelevant. -/
structure PositionalStrategy (p : Player) where
  /-- The chosen successor. -/
  next : Pos → Pos
  /-- At positions owned by `p`, the chosen successor is a legal move. -/
  legal : ∀ v, G.owner v = p → G.Move v (next v)

/-- Every player has a positional strategy, since every position has a move. -/
theorem nonempty_positionalStrategy (p : Player) : Nonempty (G.PositionalStrategy p) :=
  ⟨⟨fun v => (G.serial v).choose, fun v _ => (G.serial v).choose_spec⟩⟩

variable {G}

/-- A play conforms to a strategy of `p` if `p` always moves as the strategy prescribes. -/
def Conforms {p : Player} (σ : G.PositionalStrategy p) (π : ωSequence Pos) : Prop :=
  ∀ i, G.owner (π i) = p → π (i + 1) = σ.next (π i)

/-- The strategy `σ` of `p` wins from `v`: every play from `v` conforming to `σ` is won by `p`. -/
def WinsFrom {p : Player} (σ : G.PositionalStrategy p) (v : Pos) : Prop :=
  ∀ π, G.IsPlay π → π 0 = v → Conforms σ π → G.WonBy p π

variable (G)

/-- The positions from which player `p` has a winning positional strategy. -/
def WinningRegion (p : Player) : Set Pos :=
  { v | ∃ σ : G.PositionalStrategy p, WinsFrom σ v }

/-! ## Winners of plays -/

variable {G}

/-- With priorities bounded by `d`, every play is won by `p` or by the opponent. -/
theorem wonBy_or_wonBy_opponent {d : ℕ} (hd : ∀ v, G.priority v ≤ d) (p : Player)
    (π : ωSequence Pos) : G.WonBy p π ∨ G.WonBy p.opponent π := by
  have hb : ∀ k, (π.map G.priority) k ≤ d := fun k => hd (π k)
  cases p with
  | even => exact parityEven_or_parityOdd hb
  | odd => exact (parityEven_or_parityOdd hb).symm

/-- No play is won by both players. -/
theorem not_wonBy_and_wonBy_opponent (p : Player) (π : ωSequence Pos) :
    ¬ (G.WonBy p π ∧ G.WonBy p.opponent π) := by
  cases p with
  | even => exact not_parityEven_and_parityOdd
  | odd => exact fun h => not_parityEven_and_parityOdd ⟨h.2, h.1⟩

/-- Winning is prefix independent. -/
theorem wonBy_drop_iff (p : Player) (π : ωSequence Pos) (j : ℕ) :
    G.WonBy p (π.drop j) ↔ G.WonBy p π := by
  have hmap : (π.drop j).map G.priority = (π.map G.priority).drop j := rfl
  cases p with
  | even => exact (congrArg ParityEven hmap).to_iff.trans (parityEven_drop_iff j)
  | odd => exact (congrArg ParityOdd hmap).to_iff.trans (parityOdd_drop_iff j)

theorem IsPlay.drop {π : ωSequence Pos} (h : G.IsPlay π) (j : ℕ) : G.IsPlay (π.drop j) :=
  fun i => by simpa [get_drop, Nat.add_assoc, Nat.add_comm 1] using h (j + i)

theorem Conforms.drop {p : Player} {σ : G.PositionalStrategy p} {π : ωSequence Pos}
    (h : Conforms σ π) (j : ℕ) : Conforms σ (π.drop j) :=
  fun i hi => by simpa [get_drop, Nat.add_assoc, Nat.add_comm 1] using h (j + i) (by simpa using hi)

/-! ## The outcome of two positional strategies -/

/-- The successor chosen jointly by a strategy of `p` and a strategy of the opponent. -/
def jointNext {p : Player} (σ : G.PositionalStrategy p)
    (τ : G.PositionalStrategy p.opponent) (v : Pos) : Pos :=
  if G.owner v = p then σ.next v else τ.next v

/-- The play from `v` in which `p` follows `σ` and the opponent follows `τ`. -/
def outcome {p : Player} (σ : G.PositionalStrategy p) (τ : G.PositionalStrategy p.opponent)
    (v : Pos) : ωSequence Pos :=
  ωSequence.iterate (jointNext σ τ) v

variable {p : Player} (σ : G.PositionalStrategy p) (τ : G.PositionalStrategy p.opponent)

theorem outcome_zero (v : Pos) : outcome σ τ v 0 = v := rfl

theorem outcome_succ (v : Pos) (i : ℕ) :
    outcome σ τ v (i + 1) = jointNext σ τ (outcome σ τ v i) := by
  simp only [outcome, get_iterate, Function.iterate_succ_apply']

theorem outcome_isPlay (v : Pos) : G.IsPlay (outcome σ τ v) := by
  intro i
  rw [outcome_succ, jointNext]
  split_ifs with h
  · exact σ.legal _ h
  · exact τ.legal _ ((Player.eq_or_eq_opponent p _).resolve_left h)

theorem outcome_conforms (v : Pos) : Conforms σ (outcome σ τ v) := by
  intro i hi
  rw [outcome_succ, jointNext]
  simp [hi]

theorem outcome_conforms_opponent (v : Pos) : Conforms τ (outcome σ τ v) := by
  intro i hi
  have hne : G.owner (outcome σ τ v i) ≠ p := by
    rw [hi]
    exact Player.opponent_ne p
  rw [outcome_succ, jointNext]
  simp [hne]

variable (G) in
/-- The winning regions of the two players are disjoint. -/
theorem disjoint_winningRegion (p : Player) :
    Disjoint (G.WinningRegion p) (G.WinningRegion p.opponent) := by
  rw [Set.disjoint_left]
  rintro v ⟨σ, hσ⟩ ⟨τ, hτ⟩
  exact not_wonBy_and_wonBy_opponent p _
    ⟨hσ _ (outcome_isPlay σ τ v) rfl (outcome_conforms σ τ v),
      hτ _ (outcome_isPlay σ τ v) rfl (outcome_conforms_opponent σ τ v)⟩

/-! ## Winning strategies along moves -/

/-- If `σ` wins from `v` and `w` is a move from `v` that `σ` allows (any move if the opponent
owns `v`), then `σ` wins from `w`. -/
theorem WinsFrom.of_move {v w : Pos} (h : WinsFrom σ v) (hmove : G.Move v w)
    (hσ : G.owner v = p → w = σ.next v) : WinsFrom σ w := by
  intro π hπ h0 hconf
  have hplay : G.IsPlay (v ::ω π) := by
    intro i
    cases i with
    | zero => simpa [h0] using hmove
    | succ i => simpa using hπ i
  have hconf' : Conforms σ (v ::ω π) := by
    intro i hi
    cases i with
    | zero => simpa [h0] using hσ (by simpa using hi)
    | succ i => simpa using hconf i (by simpa using hi)
  have hwin := h _ hplay rfl hconf'
  rwa [← wonBy_drop_iff p _ 1, ← tail_eq_drop, tail_cons] at hwin

/-- Winning regions are closed under the moves of the opponent: from a position of `p`'s winning
region owned by the opponent, every move stays in the region. -/
theorem move_mem_winningRegion {v w : Pos} (hv : v ∈ G.WinningRegion p)
    (hown : G.owner v = p.opponent) (hmove : G.Move v w) : w ∈ G.WinningRegion p := by
  obtain ⟨σ, hσ⟩ := hv
  refine ⟨σ, hσ.of_move σ hmove fun h => ?_⟩
  rw [hown] at h
  exact absurd h (Player.opponent_ne p)

/-- From a position of `p`'s winning region owned by `p`, the winning strategy's move stays in
the region. -/
theorem next_mem_winningRegion {v : Pos} {σ : G.PositionalStrategy p} (hσ : WinsFrom σ v)
    (hown : G.owner v = p) : σ.next v ∈ G.WinningRegion p :=
  ⟨σ, hσ.of_move σ (σ.legal v hown) fun _ => rfl⟩

end ParityGame

end Cslib.Games
