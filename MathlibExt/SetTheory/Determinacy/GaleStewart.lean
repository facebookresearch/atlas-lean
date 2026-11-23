/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Infinite games of perfect information and the Gale–Stewart theorem

For a set `A` of moves and a payoff set `S ⊆ A^ℕ`, the game `G_A(S)` is played by two players
who alternately choose moves `x 0` (player I), `x 1` (player II), `x 2` (player I), …, each
seeing all earlier moves; player I wins the run if the resulting play `x : ℕ → A` lies in `S`,
otherwise player II wins (Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, §6A).

A strategy is a function `σ : List A → A` from finite histories to moves; a play *follows* `σ`
for player I if `x n = σ (x 0, …, x (n - 1))` at every even `n`, and for player II at every odd
`n` (Moschovakis's strategies are defined only on histories of the right parity; the values of
`σ` on the other histories are never used here). A player wins `S` if some strategy makes every
play that follows it a win for that player, and `S` is *determined* if one of the two players
wins it.

The main result is the Gale–Stewart theorem (Moschovakis 6A.2): if `A` is non-empty and `A^ℕ`
carries the product of the discrete topologies, every open and every closed payoff set is
determined. The proof is the non-losing-position argument of Moschovakis 6A.1–6A.2: the player
who wants the open set wins if he has a winning strategy from the initial position, and
otherwise his opponent can always move to a position from which he still has none, so that
the play never enters a basic open set inside the payoff.

The ambient logic of Lean includes the axiom of choice, which the proof uses (as Moschovakis's
6A.1 does) to pick the opponent's moves; for countable `A` choice is not needed mathematically.
-/

@[expose] public section

noncomputable section

open Set

namespace MathlibExt.SetTheory.Determinacy

variable {A : Type*}

/-- **History of a play.** The list `[x 0, …, x (n - 1)]` of the first `n` moves of the play
`x : ℕ → A`: the position the player to move at time `n` sees in a game of perfect
information (Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def history (x : ℕ → A) (n : ℕ) : List A :=
  List.ofFn fun i : Fin n => x i

/-- **Following a strategy at the turns of one parity.** The play `x` follows the strategy
`σ : List A → A` at the turns `n` with `n % 2 = k`: there `x n = σ (history x n)`. With
`k = 0` these are the turns of player I and with `k = 1` those of player II
(Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def Follows (k : ℕ) (σ : List A → A) (x : ℕ → A) : Prop :=
  ∀ n, n % 2 = k → x n = σ (history x n)

/-- **Player I follows a strategy.** The play `x` follows `σ` at every even turn:
`x 0 = σ []`, `x 2 = σ [x 0, x 1]`, … (Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def FollowsI (σ : List A → A) (x : ℕ → A) : Prop :=
  Follows 0 σ x

/-- **Player II follows a strategy.** The play `x` follows `τ` at every odd turn:
`x 1 = τ [x 0]`, `x 3 = τ [x 0, x 1, x 2]`, … (Moschovakis, *Descriptive Set Theory*, 2nd ed.,
§6A). -/
def FollowsII (τ : List A → A) (x : ℕ → A) : Prop :=
  Follows 1 τ x

/-- **Player I wins a game.** Player I has a winning strategy in the game with payoff
`S ⊆ A^ℕ`: a strategy `σ` such that every play following `σ` at player I's turns lies in `S`
(Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def IWins (S : Set (ℕ → A)) : Prop :=
  ∃ σ : List A → A, ∀ x, FollowsI σ x → x ∈ S

/-- **Player II wins a game.** Player II has a winning strategy in the game with payoff
`S ⊆ A^ℕ`: a strategy `τ` such that every play following `τ` at player II's turns lies
outside `S` (Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def IIWins (S : Set (ℕ → A)) : Prop :=
  ∃ τ : List A → A, ∀ x, FollowsII τ x → x ∉ S

/-- **Determined game.** The game with payoff `S ⊆ A^ℕ` is determined if one of the two players
has a winning strategy (Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). If `A` is empty
there are no strategies at all, so no set is determined. -/
def Determined (S : Set (ℕ → A)) : Prop :=
  IWins S ∨ IIWins S

/-- **The play of two strategies.** The unique play `σ * τ` in which player I follows `σ` and
player II follows `τ`: `x n = σ (history x n)` for even `n` and `x n = τ (history x n)` for odd
`n` (Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
def play (σ τ : List A → A) : ℕ → A
  | n => (if n % 2 = 0 then σ else τ) (List.ofFn fun i : Fin n => play σ τ i)
termination_by n => n
decreasing_by exact i.isLt

theorem play_eq (σ τ : List A → A) (n : ℕ) :
    play σ τ n = (if n % 2 = 0 then σ else τ) (history (play σ τ) n) := by
  rw [play]
  rfl

/-- **The play of two strategies follows the first one.** In `σ * τ` player I follows `σ`
(Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
theorem followsI_play (σ τ : List A → A) : FollowsI σ (play σ τ) := by
  intro n hn
  rw [play_eq]
  simp [hn]

/-- **The play of two strategies follows the second one.** In `σ * τ` player II follows `τ`
(Moschovakis, *Descriptive Set Theory*, 2nd ed., §6A). -/
theorem followsII_play (σ τ : List A → A) : FollowsII τ (play σ τ) := by
  intro n hn
  rw [play_eq]
  simp [show n % 2 ≠ 0 by omega]

/-- **At most one player wins.** No payoff set is won by both players: the play of the two
winning strategies would lie both in `S` and outside it (Moschovakis, *Descriptive Set
Theory*, 2nd ed., §6A). -/
theorem not_iWins_and_iiWins (S : Set (ℕ → A)) : ¬ (IWins S ∧ IIWins S) := by
  rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  exact hτ _ (followsII_play σ τ) (hσ _ (followsI_play σ τ))

/-! ### Histories -/

theorem length_history (x : ℕ → A) (n : ℕ) : (history x n).length = n := by
  simp [history]

theorem history_succ (x : ℕ → A) (n : ℕ) : history x (n + 1) = history x n ++ [x n] := by
  rw [history, history, List.ofFn_succ_last]
  rfl

theorem history_eq_history_iff {x y : ℕ → A} {n : ℕ} :
    history x n = history y n ↔ ∀ i < n, x i = y i := by
  rw [history, history, List.ofFn_inj]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.isLt

theorem history_eq_of_le {x y : ℕ → A} {m n : ℕ} (hmn : m ≤ n)
    (h : history x n = history y n) : history x m = history y m := by
  rw [history_eq_history_iff] at h ⊢
  intro i hi
  exact h i (lt_of_lt_of_le hi hmn)

theorem getElem?_history {x : ℕ → A} {n i : ℕ} (hi : i < n) : (history x n)[i]? = some (x i) := by
  simp [history, hi]

/-! ### Winning from a position, for the player of parity `k` aiming at a set `U` -/

/-- The player of parity `k` wins `U` from the position `p`: some strategy makes every play that
extends `p` and follows it at the player's turns from `p.length` on a member of `U`. -/
private def WinsFrom (k : ℕ) (U : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : List A → A, ∀ x, history x p.length = p →
    (∀ n, p.length ≤ n → n % 2 = k → x n = σ (history x n)) → x ∈ U

/-- If the player to move at `p` has a move `a` after which he wins, he wins from `p`. -/
private theorem winsFrom_of_move {k : ℕ} {U : Set (ℕ → A)} {p : List A} (hp : p.length % 2 = k)
    {a : A} (h : WinsFrom k U (p ++ [a])) : WinsFrom k U p := by
  classical
  obtain ⟨σ', hσ'⟩ := h
  refine ⟨fun q => if q = p then a else σ' q, fun x hx hfol => ?_⟩
  have hxa : x p.length = a := by
    have := hfol p.length le_rfl hp
    simpa [hx] using this
  refine hσ' x ?_ fun n hn hnk => ?_
  · simp only [List.length_append, List.length_singleton]
    rw [history_succ, hx, hxa]
  · simp only [List.length_append, List.length_singleton] at hn
    have hne : history x n ≠ p := by
      intro he
      have := congrArg List.length he
      rw [length_history] at this
      omega
    rw [hfol n (by omega) hnk]
    simp [hne]

/-- If the player wins after every next move from `p` (used when the opponent moves at `p`), he
wins from `p`. -/
private theorem winsFrom_of_forall_move [Nonempty A] {k : ℕ} {U : Set (ℕ → A)} {p : List A}
    (h : ∀ b, WinsFrom k U (p ++ [b])) : WinsFrom k U p := by
  classical
  choose σ hσ using h
  let a₀ : A := Classical.arbitrary A
  refine ⟨fun q => σ (q.getD p.length a₀) q, fun x hx hfol => ?_⟩
  refine hσ (x p.length) x ?_ fun n hn hnk => ?_
  · simp only [List.length_append, List.length_singleton]
    rw [history_succ, hx]
  · simp only [List.length_append, List.length_singleton] at hn
    have hget : (history x n).getD p.length a₀ = x p.length := by
      rw [List.getD_eq_getElem?_getD, getElem?_history (by omega)]
      rfl
    have := hfol n (by omega) hnk
    simpa only [hget] using this

/-- In the product of discrete topologies, an open set containing `x` contains every play that
agrees with `x` on some initial segment. -/
private theorem exists_history_subset [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} (hU : IsOpen U) {x : ℕ → A} (hx : x ∈ U) :
    ∃ N, ∀ y, history y N = history x N → y ∈ U := by
  obtain ⟨v, ⟨z, N, rfl⟩, hxv, hvU⟩ :=
    (PiNat.isTopologicalBasis_cylinders (E := fun _ : ℕ => A)).exists_subset_of_mem_open hx hU
  refine ⟨N, fun y hy => hvU ?_⟩
  rw [history_eq_history_iff] at hy
  rw [PiNat.mem_cylinder_iff] at hxv ⊢
  intro i hi
  rw [hy i hi, hxv i hi]

/-- Gale–Stewart for the player of parity `k` aiming at an open set `U`: either he has a
winning strategy, or his opponent has a strategy keeping every play out of `U`. -/
private theorem winsOpen_or [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    {U : Set (ℕ → A)} (hU : IsOpen U) {k : ℕ} (hk : k < 2) :
    (∃ σ : List A → A, ∀ x, Follows k σ x → x ∈ U) ∨
      (∃ τ : List A → A, ∀ x, Follows (1 - k) τ x → x ∉ U) := by
  classical
  by_cases h0 : WinsFrom k U []
  · left
    obtain ⟨σ, hσ⟩ := h0
    exact ⟨σ, fun x hx => hσ x (by simp [history]) fun n _ hn => hx n hn⟩
  · right
    let τ : List A → A := fun q =>
      if hq : ∃ b, ¬ WinsFrom k U (q ++ [b]) then hq.choose else Classical.arbitrary A
    refine ⟨τ, fun x hx hxU => ?_⟩
    -- Along a play following `τ`, the player never reaches a winning position.
    have hinv : ∀ n, ¬ WinsFrom k U (history x n) := by
      intro n
      induction n with
      | zero => simpa [history] using h0
      | succ n ih =>
        rw [history_succ]
        by_cases hn : n % 2 = k
        · intro hw
          exact ih (winsFrom_of_move (by rw [length_history]; exact hn) hw)
        · have hex : ∃ b, ¬ WinsFrom k U (history x n ++ [b]) := by
            by_contra hall
            push Not at hall
            exact ih (winsFrom_of_forall_move hall)
          have hxn : x n = τ (history x n) := hx n (by omega)
          rw [hxn]
          simp only [τ, hex, ↓reduceDIte]
          exact hex.choose_spec
    obtain ⟨N, hN⟩ := exists_history_subset hU hxU
    refine hinv N ⟨fun _ => Classical.arbitrary A, fun y hy _ => hN y ?_⟩
    rwa [length_history] at hy

/-- **Gale–Stewart theorem, open case.** If the set of moves `A` is non-empty and `A^ℕ` carries
the product of the discrete topologies, every open payoff set `S ⊆ A^ℕ` is determined
(Gale and Stewart, *Infinite games with perfect information*, Ann. of Math. Stud. 28 (1953);
Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, Theorem 6A.2 and 6A.4). -/
theorem determined_of_isOpen [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    {S : Set (ℕ → A)} (hS : IsOpen S) : Determined S :=
  winsOpen_or hS (k := 0) (by norm_num)

/-- **Gale–Stewart theorem.** If the set of moves `A` is non-empty and `A^ℕ` carries the
product of the discrete topologies, every closed payoff set `S ⊆ A^ℕ` is determined
(Gale and Stewart, *Infinite games with perfect information*, Ann. of Math. Stud. 28 (1953);
Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, Theorem 6A.2). -/
theorem determined_of_isClosed [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    {S : Set (ℕ → A)} (hS : IsClosed S) : Determined S := by
  rcases winsOpen_or hS.isOpen_compl (k := 1) (by norm_num) with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inr ⟨σ, fun x hx => hσ x hx⟩
  · exact Or.inl ⟨τ, fun x hx => by simpa using hτ x hx⟩

/-- **Games with a single move are determined.** If `A` has exactly one element, there is a
single play, and every payoff set is determined: player I wins if it contains that play and
player II wins otherwise. This degenerate case shows why the existence of non-determined sets
needs at least two moves. -/
theorem determined_of_subsingleton [Nonempty A] [Subsingleton A] (S : Set (ℕ → A)) :
    Determined S := by
  let a : A := Classical.arbitrary A
  by_cases h : (fun _ => a) ∈ S
  · refine Or.inl ⟨fun _ => a, fun x _ => ?_⟩
    rwa [show x = fun _ => a from funext fun _ => Subsingleton.elim _ _]
  · refine Or.inr ⟨fun _ => a, fun x _ => ?_⟩
    rwa [show x = fun _ => a from funext fun _ => Subsingleton.elim _ _]

end MathlibExt.SetTheory.Determinacy
