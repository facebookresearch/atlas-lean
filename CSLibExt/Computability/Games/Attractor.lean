/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Attractors and traps in parity games
-/
module

public import CSLibExt.Computability.Games.Parity
public import Mathlib.Data.Set.Card
public import Mathlib.Order.FixedPoints

/-!
# Attractors and traps in parity games

The attractor of a set `T` for a player `p` is the set of positions from which `p` can force
the play into `T`. It is the least fixed point of `X ↦ T ∪ cpre p X`, where the *controllable
predecessor* `cpre p X` holds the positions of `p` with some move into `X` and the positions of
the opponent with all moves into `X`. A *`p`-trap* is a set that `p` cannot force the play to
leave: positions of `p` in it have all their moves in it, positions of the opponent some move.

Main definitions, on the phase-1 arena `Cslib.Games.ParityGame` (priorities play no role here):

* `ParityGame.cpre`, `ParityGame.attractor` (the least fixed point `OrderHom.lfp`), and its
  approximations `ParityGame.attractorStage`, the iterates of the attractor operator from `∅`.
* `ParityGame.attractorStrategy`: a positional strategy for `p` moving to a lowest stage.
* `ParityGame.ForcesReach σ T v`: every play from `v` conforming to `σ` visits `T`.
* `ParityGame.IsTrap p U` and `ParityGame.trapStrategy`: the opponent's positional strategy
  staying in a set.

Main results:

* `attractor_eq_attractorStage_card`: on a finite arena the attractor is reached after
  `Nat.card Pos` iterations, so it is a finite least fixed point.
* `attractorStrategy_reaches`, `forcesReach_attractorStrategy`: from the `n`-th stage the
  attractor strategy reaches `T` within `n` moves; on a finite arena it forces a visit to `T`
  from every position of the attractor.
* `isTrap_compl_attractor`: the complement of an attractor is a trap for the attracting player,
  and `IsTrap.trapStrategy_stays` keeps the opponent in a trap forever, so from outside the
  attractor no strategy of `p` forces a visit to `T` (`not_forcesReach_of_notMem_attractor`).
* `mem_attractor_iff`: on a finite arena the attractor is exactly the set of positions from which
  `p` has a positional strategy forcing a visit to `T`.
* `IsTrap.disjoint_attractor`: a `p`-trap disjoint from `T` is disjoint from the attractor, so
  the complement of the attractor is the largest such trap; `isTrap_winningRegion`: a winning
  region of `p` is a trap for the opponent.

These are the ingredients of Zielonka's proof of positional determinacy, which is not done here.

## References

* E. Grädel, W. Thomas, T. Wilke (eds.), *Automata, Logics, and Infinite Games*, LNCS 2500,
  Springer, 2002, Chapter 2 ("Infinite Games").
* W. Zielonka, *Infinite games on finitely coloured graphs with applications to automata on
  infinite trees*, Theoretical Computer Science 200 (1998), 135–183.
-/

@[expose] public section

namespace Cslib.Games.ParityGame

open ωSequence

variable {Pos : Type*} (G : ParityGame Pos)

/-! ## The attractor as a least fixed point -/

/-- **Controllable predecessor.** Let $G$ be a parity game, $p$ a player and $X$ a set of
positions. The controllable predecessor $\mathrm{cpre}_p(X)$ of $X$ for $p$ is the set of
positions $v$ such that either $v$ is owned by $p$ and some move from $v$ leads into $X$, or $v$
is not owned by $p$ and every move from $v$ leads into $X$. -/
def cpre (p : Player) (X : Set Pos) : Set Pos :=
  { v | (G.owner v = p ∧ ∃ w, G.Move v w ∧ w ∈ X) ∨ (G.owner v ≠ p ∧ ∀ w, G.Move v w → w ∈ X) }

theorem cpre_mono (p : Player) : Monotone (G.cpre p) := by
  intro X Y hXY v hv
  rcases hv with ⟨ho, w, hw, hX⟩ | ⟨ho, hall⟩
  · exact Or.inl ⟨ho, w, hw, hXY hX⟩
  · exact Or.inr ⟨ho, fun w hw => hXY (hall w hw)⟩

/-- **Attractor operator.** Let $G$ be a parity game, $p$ a player and $T$ a set of positions. The
attractor operator of $T$ for $p$ is the monotone map on sets of positions sending $X$ to
$T \cup \mathrm{cpre}_p(X)$, where $\mathrm{cpre}_p$ is the controllable predecessor for $p$. -/
def attractorStep (p : Player) (T : Set Pos) : Set Pos →o Set Pos where
  toFun X := T ∪ G.cpre p X
  monotone' _ _ h := Set.union_subset_union_right T (G.cpre_mono p h)

/-- **Attractor.** Let $G$ be a parity game, $p$ a player and $T$ a set of positions. The
attractor of $T$ for $p$ is the least fixed point of the attractor operator
$X \mapsto T \cup \mathrm{cpre}_p(X)$ on sets of positions, where $\mathrm{cpre}_p$ is the
controllable predecessor for $p$. -/
def attractor (p : Player) (T : Set Pos) : Set Pos :=
  OrderHom.lfp (G.attractorStep p T)

/-- **Attractor stages.** Let $G$ be a parity game, $p$ a player, $T$ a set of positions and $n$ a
natural number. The $n$-th attractor stage $S_n$ of $T$ for $p$ is the set obtained by applying the
attractor operator $X \mapsto T \cup \mathrm{cpre}_p(X)$ $n$ times to $\emptyset$, where
$\mathrm{cpre}_p$ is the controllable predecessor for $p$; thus $S_0 = \emptyset$ and
$S_{n+1} = T \cup \mathrm{cpre}_p(S_n)$.

The $n$-th stage consists of the positions from which $p$ can force a visit to $T$ within fewer
than $n$ moves. -/
def attractorStage (p : Player) (T : Set Pos) (n : ℕ) : Set Pos :=
  (G.attractorStep p T)^[n] ∅

variable (p : Player) (T : Set Pos)

@[simp] theorem attractorStage_zero : G.attractorStage p T 0 = ∅ := rfl

theorem attractorStage_succ (n : ℕ) :
    G.attractorStage p T (n + 1) = T ∪ G.cpre p (G.attractorStage p T n) :=
  Function.iterate_succ_apply' _ _ _

theorem attractorStage_mono : Monotone (G.attractorStage p T) :=
  (G.attractorStep p T).monotone.monotone_iterate_of_le_map (Set.empty_subset _)

/-- **The attractor is a fixed point.** Let $G$ be a parity game, $p$ a player and $T$ a set of
positions, and let $A$ be the attractor of $T$ for $p$. Then $T \cup \mathrm{cpre}_p(A) = A$, where
$\mathrm{cpre}_p(A)$ is the controllable predecessor of $A$ for $p$; that is, $A$ is a fixed point
of the attractor operator $X \mapsto T \cup \mathrm{cpre}_p(X)$. -/
theorem union_cpre_attractor : T ∪ G.cpre p (G.attractor p T) = G.attractor p T :=
  OrderHom.map_lfp (G.attractorStep p T)

/-- **The attractor lies in every closed set.** Let $G$ be a parity game, $p$ a player and $T$ a
set of positions. If a set $X$ of positions satisfies $T \cup \mathrm{cpre}_p(X) \subseteq X$,
where $\mathrm{cpre}_p$ is the controllable predecessor for $p$, then the attractor of $T$ for $p$
is contained in $X$. -/
theorem attractor_subset_of {X : Set Pos} (h : T ∪ G.cpre p X ⊆ X) : G.attractor p T ⊆ X :=
  OrderHom.lfp_le _ h

theorem subset_attractor : T ⊆ G.attractor p T := fun v hv => by
  rw [← G.union_cpre_attractor]
  exact Or.inl hv

theorem cpre_attractor_subset : G.cpre p (G.attractor p T) ⊆ G.attractor p T := fun v hv => by
  rw [← G.union_cpre_attractor]
  exact Or.inr hv

theorem attractor_mono {T T' : Set Pos} (h : T ⊆ T') : G.attractor p T ⊆ G.attractor p T' :=
  G.attractor_subset_of p T
    (Set.union_subset (h.trans (G.subset_attractor p T')) (G.cpre_attractor_subset p T'))

theorem attractorStage_subset_attractor (n : ℕ) : G.attractorStage p T n ⊆ G.attractor p T := by
  induction n with
  | zero => exact Set.empty_subset _
  | succ n ih =>
    rw [attractorStage_succ, ← G.union_cpre_attractor]
    exact Set.union_subset_union_right T (G.cpre_mono p ih)

/-- Until the stages stop growing, the `n`-th stage has at least `n` positions. -/
private theorem attractorStage_stable_or_le_ncard [Finite Pos] (n : ℕ) :
    (∃ m < n, G.attractorStage p T (m + 1) = G.attractorStage p T m) ∨
      n ≤ (G.attractorStage p T n).ncard := by
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    rcases ih with ⟨m, hm, hstable⟩ | hle
    · exact Or.inl ⟨m, by omega, hstable⟩
    · by_cases hstable : G.attractorStage p T (n + 1) = G.attractorStage p T n
      · exact Or.inl ⟨n, by omega, hstable⟩
      · refine Or.inr (Nat.succ_le_of_lt (hle.trans_lt (Set.ncard_lt_ncard ?_)))
        exact (G.attractorStage_mono p T (Nat.le_succ n)).ssubset_of_ne (Ne.symm hstable)

/-- Once two consecutive stages agree, all later stages agree. -/
private theorem attractorStage_eq_of_stable {m : ℕ}
    (h : G.attractorStage p T (m + 1) = G.attractorStage p T m) (k : ℕ) :
    G.attractorStage p T (m + k) = G.attractorStage p T m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, attractorStage_succ, ih, ← attractorStage_succ, h]

/-- **The attractor stabilizes after as many stages as there are positions.** Let $G$ be a parity
game with finitely many positions, $N$ of them, let $p$ be a player and $T$ a set of positions.
Then the attractor of $T$ for $p$ equals the $N$-th attractor stage of $T$ for $p$, that is, the
result of applying the attractor operator $X \mapsto T \cup \mathrm{cpre}_p(X)$ $N$ times to
$\emptyset$, where $\mathrm{cpre}_p$ is the controllable predecessor for $p$. -/
theorem attractor_eq_attractorStage_card [Finite Pos] :
    G.attractor p T = G.attractorStage p T (Nat.card Pos) := by
  refine (G.attractor_subset_of p T ?_).antisymm (G.attractorStage_subset_attractor p T _)
  rw [← attractorStage_succ]
  rcases G.attractorStage_stable_or_le_ncard p T (Nat.card Pos + 1) with ⟨m, hm, hstable⟩ | hle
  · obtain ⟨k, hk⟩ : ∃ k, Nat.card Pos = m + k := ⟨Nat.card Pos - m, by omega⟩
    rw [hk, show m + k + 1 = m + (k + 1) by omega,
      G.attractorStage_eq_of_stable p T hstable (k + 1),
      G.attractorStage_eq_of_stable p T hstable k]
  · have := Set.ncard_le_ncard (Set.subset_univ (G.attractorStage p T (Nat.card Pos + 1)))
    rw [Set.ncard_univ] at this
    omega

/-! ## Attractor strategies -/

open Classical in
/-- **Attractor strategy.** Let $G$ be a parity game, $p$ a player and $T$ a set of positions. The
attractor strategy of $p$ for $T$ is the positional strategy of $p$ that at a position $v$ moves
to a successor of $v$ lying in the $n$-th attractor stage of $T$ for $p$, for the least $n$ for
which $v$ has such a successor, and to an arbitrary successor of $v$ if no successor of $v$ lies
in any attractor stage. -/
noncomputable def attractorStrategy : G.PositionalStrategy p where
  next v :=
    if h : ∃ n w, G.Move v w ∧ w ∈ G.attractorStage p T n then (Nat.find_spec h).choose
    else (G.serial v).choose
  legal v _ := by
    split_ifs with h
    · exact (Nat.find_spec h).choose_spec.1
    · exact (G.serial v).choose_spec

variable {G p T}

/-- **The attractor strategy moves into the stage from its controllable predecessor.** Let $G$ be
a parity game, $p$ a player, $T$ a set of positions, $n$ a natural number and $S_n$ the $n$-th
attractor stage of $T$ for $p$. If a position $v$ owned by $p$ lies in the controllable
predecessor $\mathrm{cpre}_p(S_n)$ of $S_n$ for $p$, then the successor that the attractor
strategy of $p$ for $T$ chooses at $v$ lies in $S_n$. -/
theorem attractorStrategy_next_mem {n : ℕ} {v : Pos}
    (hv : v ∈ G.cpre p (G.attractorStage p T n)) (hown : G.owner v = p) :
    (G.attractorStrategy p T).next v ∈ G.attractorStage p T n := by
  classical
  obtain ⟨w, hw, hwX⟩ : ∃ w, G.Move v w ∧ w ∈ G.attractorStage p T n := by
    rcases hv with ⟨_, hex⟩ | ⟨hne, _⟩
    · exact hex
    · exact absurd hown hne
  have h : ∃ n w, G.Move v w ∧ w ∈ G.attractorStage p T n := ⟨n, w, hw, hwX⟩
  have hnext : (G.attractorStrategy p T).next v = (Nat.find_spec h).choose := dite_eq_left h
  rw [hnext]
  exact G.attractorStage_mono p T (Nat.find_min' h ⟨w, hw, hwX⟩) (Nat.find_spec h).choose_spec.2

/-- **The attractor strategy reaches the target from an attractor stage.** Let $G$ be a parity
game, $p$ a player, $T$ a set of positions and $n$ a natural number. If $\pi$ is a play of $G$
that conforms to the attractor strategy of $p$ for $T$ and whose initial position $\pi_0$ lies in
the $n$-th attractor stage of $T$ for $p$, then $\pi_i \in T$ for some $i < n$. -/
theorem attractorStrategy_reaches (n : ℕ) {π : ωSequence Pos} (hπ : G.IsPlay π)
    (hconf : Conforms (G.attractorStrategy p T) π) (h0 : π 0 ∈ G.attractorStage p T n) :
    ∃ i < n, π i ∈ T := by
  induction n generalizing π with
  | zero => exact absurd h0 (Set.notMem_empty _)
  | succ n ih =>
    rw [attractorStage_succ] at h0
    rcases h0 with hT | hc
    · exact ⟨0, Nat.succ_pos n, hT⟩
    · have h1 : π 1 ∈ G.attractorStage p T n := by
        by_cases hown : G.owner (π 0) = p
        · rw [hconf 0 hown]
          exact attractorStrategy_next_mem hc hown
        · rcases hc with ⟨h', _⟩ | ⟨_, hall⟩
          · exact absurd h' hown
          · exact hall _ (hπ 0)
      obtain ⟨i, hi, hiT⟩ := ih (hπ.drop 1) (hconf.drop 1) (by simpa [get_drop] using h1)
      exact ⟨1 + i, by omega, by simpa [get_drop] using hiT⟩

variable (G) in
/-- **Forcing a visit to a set.** Let $G$ be a parity game, $p$ a player, $\sigma$ a positional
strategy of $p$, $T$ a set of positions and $v$ a position. The strategy $\sigma$ forces a visit
to $T$ from $v$ when every play $\pi$ of $G$ with $\pi_0 = v$ that conforms to $\sigma$ visits
$T$, that is, $\pi_i \in T$ for some $i \in \mathbb{N}$. -/
def ForcesReach {p : Player} (σ : G.PositionalStrategy p) (T : Set Pos) (v : Pos) : Prop :=
  ∀ π, G.IsPlay π → π 0 = v → Conforms σ π → ∃ i, π i ∈ T

/-- **The attractor strategy reaches the target from the attractor.** Let $G$ be a parity game
with finitely many positions, $N$ of them, let $p$ be a player and $T$ a set of positions. If
$\pi$ is a play of $G$ that conforms to the attractor strategy of $p$ for $T$ and whose initial
position $\pi_0$ lies in the attractor of $T$ for $p$, then $\pi_i \in T$ for some $i < N$. -/
theorem attractorStrategy_reaches_of_mem_attractor [Finite Pos] {π : ωSequence Pos}
    (hπ : G.IsPlay π) (hconf : Conforms (G.attractorStrategy p T) π)
    (h0 : π 0 ∈ G.attractor p T) : ∃ i < Nat.card Pos, π i ∈ T := by
  rw [attractor_eq_attractorStage_card] at h0
  exact attractorStrategy_reaches _ hπ hconf h0

/-- **The attractor strategy forces a visit.** Let $G$ be a parity game with finitely many
positions, $p$ a player and $T$ a set of positions. From every position $v$ of the attractor of
$T$ for $p$, the attractor strategy of $p$ for $T$ forces a visit to $T$: every play from $v$
conforming to it visits $T$. -/
theorem forcesReach_attractorStrategy [Finite Pos] {v : Pos} (hv : v ∈ G.attractor p T) :
    G.ForcesReach (G.attractorStrategy p T) T v := fun _ hπ h0 hconf =>
  let ⟨i, _, hi⟩ := attractorStrategy_reaches_of_mem_attractor hπ hconf (h0 ▸ hv)
  ⟨i, hi⟩

/-! ## Traps -/

variable (G p) in
/-- **Trap for a player.** Let $G$ be a parity game and $p$ a player. A set $U$ of positions is a
trap for $p$ when, for every position $v \in U$, every move from $v$ leads into $U$ if $v$
belongs to $p$, and some move from $v$ leads into $U$ if $v$ does not belong to $p$. Thus $p$
cannot force the play out of $U$. -/
def IsTrap (U : Set Pos) : Prop :=
  ∀ v ∈ U, (G.owner v = p → ∀ w, G.Move v w → w ∈ U) ∧ (G.owner v ≠ p → ∃ w, G.Move v w ∧ w ∈ U)

variable (G p T) in
/-- **The complement of an attractor is a trap.** Let $G$ be a parity game, $p$ a player and $T$
a set of positions. The complement of the attractor of $T$ for $p$ is a trap for $p$. -/
theorem isTrap_compl_attractor : G.IsTrap p (G.attractor p T)ᶜ := by
  intro v hv
  have hv' : v ∉ G.cpre p (G.attractor p T) := fun h => hv (G.cpre_attractor_subset p T h)
  refine ⟨fun hown w hw hwA => hv' (Or.inl ⟨hown, w, hw, hwA⟩), fun hown => ?_⟩
  by_contra hcon
  exact hv' (Or.inr ⟨hown, fun w hw => by_contra fun hw' => hcon ⟨w, hw, hw'⟩⟩)

/-- **Traps disjoint from a set avoid its attractor.** Let $G$ be a parity game, $p$ a player and
$T$ a set of positions. If a set $U$ of positions is a trap for $p$ and is disjoint from $T$, then
$U$ is disjoint from the attractor of $T$ for $p$.

Since the complement of the attractor is itself a trap for $p$ disjoint from $T$, it is the
largest such trap. -/
theorem IsTrap.disjoint_attractor {U : Set Pos} (hU : G.IsTrap p U) (hT : Disjoint U T) :
    Disjoint U (G.attractor p T) := by
  rw [← Set.subset_compl_iff_disjoint_left]
  refine G.attractor_subset_of p T (Set.union_subset ?_ ?_)
  · exact Set.subset_compl_iff_disjoint_left.mpr hT
  · intro v hv hvU
    rcases hv with ⟨hown, w, hw, hwU⟩ | ⟨hown, hall⟩
    · exact hwU ((hU v hvU).1 hown w hw)
    · obtain ⟨w, hw, hwU⟩ := (hU v hvU).2 hown
      exact hall w hw hwU

variable (G p) in
open Classical in
/-- **Trap strategy.** Let $G$ be a parity game, $p$ a player and $U$ a set of positions. The trap
strategy for $U$ is the positional strategy of the opponent of $p$ that, at each position $v$,
moves to some position $w \in U$ with a move from $v$ to $w$ if there is one, and to an arbitrary
position reachable from $v$ in one move otherwise. -/
noncomputable def trapStrategy (U : Set Pos) : G.PositionalStrategy p.opponent where
  next v := if h : ∃ w, G.Move v w ∧ w ∈ U then h.choose else (G.serial v).choose
  legal v _ := by
    split_ifs with h
    · exact h.choose_spec.1
    · exact (G.serial v).choose_spec

theorem trapStrategy_next_mem {U : Set Pos} {v : Pos} (h : ∃ w, G.Move v w ∧ w ∈ U) :
    (G.trapStrategy p U).next v ∈ U := by
  classical
  have hnext : (G.trapStrategy p U).next v = h.choose := dite_eq_left h
  rw [hnext]
  exact h.choose_spec.2

/-- **The trap strategy stays in the trap.** Let $G$ be a parity game, $p$ a player and $U$ a trap
for $p$. If $\pi$ is a play with $\pi_0 \in U$ that conforms to the trap strategy of the opponent
of $p$ for $U$, then $\pi_i \in U$ for every $i \in \mathbb{N}$. -/
theorem IsTrap.trapStrategy_stays {U : Set Pos} (hU : G.IsTrap p U) {π : ωSequence Pos}
    (hπ : G.IsPlay π) (hconf : Conforms (G.trapStrategy p U) π) (h0 : π 0 ∈ U) (i : ℕ) :
    π i ∈ U := by
  induction i with
  | zero => exact h0
  | succ i ih =>
    by_cases hown : G.owner (π i) = p
    · exact (hU _ ih).1 hown _ (hπ i)
    · rw [hconf i ((Player.eq_or_eq_opponent p _).resolve_left hown)]
      exact trapStrategy_next_mem ((hU _ ih).2 hown)

/-- **The trap strategy avoids the target.** Let $G$ be a parity game, $p$ a player, $T$ a set of
positions and $A$ the attractor of $T$ for $p$. If $\pi$ is a play starting at a position outside
$A$ that conforms to the trap strategy of the opponent of $p$ for the complement of $A$, then
$\pi_i \notin T$ for every $i \in \mathbb{N}$. -/
theorem trapStrategy_avoids {v : Pos} (hv : v ∉ G.attractor p T) {π : ωSequence Pos}
    (hπ : G.IsPlay π) (h0 : π 0 = v) (hconf : Conforms (G.trapStrategy p (G.attractor p T)ᶜ) π)
    (i : ℕ) : π i ∉ T := fun hT =>
  (isTrap_compl_attractor G p T).trapStrategy_stays hπ hconf (h0 ▸ hv) i
    (G.subset_attractor p T hT)

/-- **No strategy forces a visit from outside the attractor.** Let $G$ be a parity game, $p$ a
player and $T$ a set of positions. If a position $v$ is not in the attractor of $T$ for $p$, then
no positional strategy of $p$ forces a visit to $T$ from $v$. -/
theorem not_forcesReach_of_notMem_attractor {v : Pos} (hv : v ∉ G.attractor p T)
    (σ : G.PositionalStrategy p) : ¬ G.ForcesReach σ T v := fun h => by
  let τ := G.trapStrategy p (G.attractor p T)ᶜ
  obtain ⟨i, hi⟩ := h _ (outcome_isPlay σ τ v) rfl (outcome_conforms σ τ v)
  exact trapStrategy_avoids hv (outcome_isPlay σ τ v) rfl (outcome_conforms_opponent σ τ v) i hi

/-- **Characterization of the attractor.** Let $G$ be a parity game with finitely many positions,
$p$ a player and $T$ a set of positions. A position $v$ lies in the attractor of $T$ for $p$ if
and only if some positional strategy of $p$ forces a visit to $T$ from $v$. -/
theorem mem_attractor_iff [Finite Pos] {v : Pos} :
    v ∈ G.attractor p T ↔ ∃ σ : G.PositionalStrategy p, G.ForcesReach σ T v :=
  ⟨fun hv => ⟨_, forcesReach_attractorStrategy hv⟩, fun ⟨σ, hσ⟩ => by
    by_contra hv
    exact not_forcesReach_of_notMem_attractor hv σ hσ⟩

variable (G p) in
/-- **Winning regions are traps for the opponent.** In a parity game $G$, the winning region of a
player $p$, the set of positions from which $p$ has a winning positional strategy, is a trap for
the opponent of $p$. -/
theorem isTrap_winningRegion : G.IsTrap p.opponent (G.WinningRegion p) := by
  intro v hv
  refine ⟨fun hown _ hmove => move_mem_winningRegion hv hown hmove, fun hown => ?_⟩
  have hp : G.owner v = p := (Player.eq_or_eq_opponent p _).resolve_right hown
  obtain ⟨σ, hσ⟩ := hv
  exact ⟨σ.next v, σ.legal v hp, next_mem_winningRegion hσ hp⟩

end Cslib.Games.ParityGame
