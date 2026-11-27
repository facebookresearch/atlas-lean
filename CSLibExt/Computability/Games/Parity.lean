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

/-- **Players of a parity game.** A parity game has exactly two players, the even player and the
odd player.

The even player is the one who wins the plays whose largest priority occurring infinitely often
is even, and the odd player the one who wins those where it is odd. -/
inductive Player where
  /-- The player who wins plays whose maximal recurring priority is even. -/
  | even
  /-- The player who wins plays whose maximal recurring priority is odd. -/
  | odd
  deriving DecidableEq, Repr

namespace Player

/-- **Opponent.** The opponent of a player of a parity game is the other player: the opponent
of the even player is the odd player, and the opponent of the odd player is the even player. -/
def opponent : Player → Player
  | even => odd
  | odd => even

@[simp] theorem opponent_even : opponent even = odd := rfl

@[simp] theorem opponent_odd : opponent odd = even := rfl

@[simp] theorem opponent_opponent (p : Player) : p.opponent.opponent = p := by
  cases p <;> rfl

theorem opponent_ne (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

/-- **Every player is $p$ or the opponent of $p$.** For all players $p$ and $q$ of a parity game,
$q = p$ or $q$ is the opponent of $p$. -/
theorem eq_or_eq_opponent (p q : Player) : q = p ∨ q = p.opponent := by
  cases p <;> cases q <;> simp

/-- **Parity winning condition of a player.** A player wins an infinite sequence of
natural-number priorities when the sequence satisfies that player's parity condition: the even
player wins it when the largest priority occurring infinitely often exists and is even, and the
odd player wins it when the largest priority occurring infinitely often exists and is odd. -/
def Wins : Player → ωSequence ℕ → Prop
  | even, ps => ParityEven ps
  | odd, ps => ParityOdd ps

end Player

/-- **Parity game.** A parity game on a type of positions consists of an owner for each
position, which is one of the two players, a move relation between positions, where the owner of
$v$ may move from $v$ to $w$ when $v$ is related to $w$, and a natural-number priority for each
position, such that every position has at least one move (there are no dead ends).

As in the usual infinite-play model, the absence of dead ends means that both players always
have positional strategies. -/
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

/-- **Plays of a parity game.** An infinite sequence of positions $\pi_0, \pi_1, \dots$ of a
parity game is a play if for every $i$ there is a move from $\pi_i$ to $\pi_{i+1}$. -/
def IsPlay (π : ωSequence Pos) : Prop :=
  ∀ i, G.Move (π i) (π (i + 1))

/-- **Winner of a play in a parity game.** Let $G$ be a parity game, write $\Omega(v)$ for the
priority of a position $v$, and let $p$ be a player. An infinite sequence
$\pi = \pi_0 \pi_1 \pi_2 \dots$ of positions of $G$ is won by $p$ when its priority sequence
$\Omega(\pi_0) \Omega(\pi_1) \Omega(\pi_2) \dots$ satisfies the parity condition of $p$: among
the priorities occurring infinitely often there is a largest one, and it is even if $p$ is the
even player and odd if $p$ is the odd player.

The definition applies to every infinite sequence of positions, whether or not it follows the
moves of $G$. -/
def WonBy (p : Player) (π : ωSequence Pos) : Prop :=
  p.Wins (π.map G.priority)

/-- A positional (memoryless) strategy for player `p`: a choice of successor at each position,
legal at the positions `p` owns. Its values elsewhere are irrelevant. -/
structure PositionalStrategy (p : Player) where
  /-- The chosen successor. -/
  next : Pos → Pos
  /-- At positions owned by `p`, the chosen successor is a legal move. -/
  legal : ∀ v, G.owner v = p → G.Move v (next v)

/-- **Positional strategies exist.** In a parity game, every player has a positional strategy,
since every position has a move. -/
theorem nonempty_positionalStrategy (p : Player) : Nonempty (G.PositionalStrategy p) :=
  ⟨⟨fun v => (G.serial v).choose, fun v _ => (G.serial v).choose_spec⟩⟩

variable {G}

/-- **Plays conforming to a strategy.** Let $\sigma$ be a positional strategy of player $p$ in a
parity game. An infinite sequence of positions $\pi_0, \pi_1, \dots$ (not necessarily a play)
conforms to $\sigma$ if $\pi_{i+1} = \sigma(\pi_i)$ for every $i$ such that $p$ owns $\pi_i$. -/
def Conforms {p : Player} (σ : G.PositionalStrategy p) (π : ωSequence Pos) : Prop :=
  ∀ i, G.owner (π i) = p → π (i + 1) = σ.next (π i)

/-- **Winning strategy from a position.** Let $p$ be a player of a parity game. A positional
strategy $\sigma$ of $p$ wins from a position $v$ when every play starting at $v$ that conforms
to $\sigma$ (at every position owned by $p$, the play moves to the successor chosen by $\sigma$)
is won by $p$. -/
def WinsFrom {p : Player} (σ : G.PositionalStrategy p) (v : Pos) : Prop :=
  ∀ π, G.IsPlay π → π 0 = v → Conforms σ π → G.WonBy p π

variable (G)

/-- The positions from which player `p` has a winning positional strategy. -/
def WinningRegion (p : Player) : Set Pos :=
  { v | ∃ σ : G.PositionalStrategy p, WinsFrom σ v }

/-! ## Winners of plays -/

variable {G}

/-- **Bounded priorities give every play a winner.** Let $p$ be a player of a parity game in
which every position has priority at most $d$, for some natural number $d$. Then every infinite
sequence of positions, in particular every play, is won by $p$ or by the opponent of $p$. -/
theorem wonBy_or_wonBy_opponent {d : ℕ} (hd : ∀ v, G.priority v ≤ d) (p : Player)
    (π : ωSequence Pos) : G.WonBy p π ∨ G.WonBy p.opponent π := by
  have hb : ∀ k, (π.map G.priority) k ≤ d := fun k => hd (π k)
  cases p with
  | even => exact parityEven_or_parityOdd hb
  | odd => exact (parityEven_or_parityOdd hb).symm

/-- **No play is won by both players.** In a parity game, for every player $p$, no infinite
sequence of positions (play or not) is won both by $p$ and by the opponent of $p$. -/
theorem not_wonBy_and_wonBy_opponent (p : Player) (π : ωSequence Pos) :
    ¬ (G.WonBy p π ∧ G.WonBy p.opponent π) := by
  cases p with
  | even => exact not_parityEven_and_parityOdd
  | odd => exact fun h => not_parityEven_and_parityOdd ⟨h.2, h.1⟩

/-- **Winning is prefix independent.** Let $p$ be a player of a parity game, $\pi = (\pi_0,
\pi_1, \dots)$ an infinite sequence of positions and $j$ a natural number. Then the sequence
$(\pi_j, \pi_{j+1}, \dots)$, obtained by dropping the first $j$ positions of $\pi$, is won by $p$
if and only if $\pi$ is won by $p$. -/
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

/-- **Joint successor of two strategies.** Let $\sigma$ be a positional strategy of player $p$
and $\tau$ a positional strategy of the opponent of $p$ in a parity game. The joint successor of
a position $v$ is $\sigma(v)$ if $p$ owns $v$, and $\tau(v)$ otherwise. -/
def jointNext {p : Player} (σ : G.PositionalStrategy p)
    (τ : G.PositionalStrategy p.opponent) (v : Pos) : Pos :=
  if G.owner v = p then σ.next v else τ.next v

/-- **Outcome of two positional strategies.** Let $p$ be a player of a parity game, $\sigma$ a
positional strategy of $p$ and $\tau$ a positional strategy of the opponent of $p$. The outcome
of $\sigma$ and $\tau$ from a position $v$ is the infinite sequence of positions
$v_0, v_1, v_2, \dots$ with $v_0 = v$ in which $v_{i+1}$ is the successor chosen by $\sigma$ at
$v_i$ if $p$ owns $v_i$, and the successor chosen by $\tau$ at $v_i$ otherwise. It is the play
from $v$ in which $p$ follows $\sigma$ and the opponent follows $\tau$. -/
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
/-- **The winning regions of the two players are disjoint.** In a parity game, for every player
$p$, no position lies both in the winning region of $p$ and in the winning region of the
opponent of $p$. -/
theorem disjoint_winningRegion (p : Player) :
    Disjoint (G.WinningRegion p) (G.WinningRegion p.opponent) := by
  rw [Set.disjoint_left]
  rintro v ⟨σ, hσ⟩ ⟨τ, hτ⟩
  exact not_wonBy_and_wonBy_opponent p _
    ⟨hσ _ (outcome_isPlay σ τ v) rfl (outcome_conforms σ τ v),
      hτ _ (outcome_isPlay σ τ v) rfl (outcome_conforms_opponent σ τ v)⟩

/-! ## Winning strategies along moves -/

/-- **Winning strategies keep winning along allowed moves.** In a parity game, let $\sigma$ be a
positional strategy of player $p$ that wins from a position $v$, and let $w$ be a position with a
move from $v$ to $w$ such that $w = \sigma(v)$ if $p$ owns $v$. Then $\sigma$ wins from $w$. -/
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

/-- **Opponent moves stay in the winning region.** In a parity game, let $v$ be a position in the
winning region of player $p$ that is owned by the opponent of $p$. Then every position $w$ with a
move from $v$ to $w$ is in the winning region of $p$. -/
theorem move_mem_winningRegion {v w : Pos} (hv : v ∈ G.WinningRegion p)
    (hown : G.owner v = p.opponent) (hmove : G.Move v w) : w ∈ G.WinningRegion p := by
  obtain ⟨σ, hσ⟩ := hv
  refine ⟨σ, hσ.of_move σ hmove fun h => ?_⟩
  rw [hown] at h
  exact absurd h (Player.opponent_ne p)

/-- **A winning strategy's move stays in the winning region.** In a parity game, let $\sigma$ be a
positional strategy of player $p$ that wins from a position $v$ owned by $p$. Then the successor
$\sigma(v)$ chosen by $\sigma$ is in the winning region of $p$. -/
theorem next_mem_winningRegion {v : Pos} {σ : G.PositionalStrategy p} (hσ : WinsFrom σ v)
    (hown : G.owner v = p) : σ.next v ∈ G.WinningRegion p :=
  ⟨σ, hσ.of_move σ (σ.legal v hown) fun _ => rfl⟩

end ParityGame

end Cslib.Games
