/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Asynchronous message-passing systems

The basic asynchronous message-passing model. Processes range over a type `P`, their states over
`Q` and messages over `M`; the processes are the nodes of a directed network `G : Digraph P`.

* `Config`: a configuration gives the state of every process and, for every ordered pair `i, j`,
  the channel `chan i j`, the multiset of messages sent from `i` to `j` and not yet delivered.
* `Event`: in an event, one process receives a multiset of messages, each paired with its sender,
  and takes a step. It is a delivery event when it delivers a message and a computation event when
  it delivers none.
* `Protocol`: each process has a set of initial states and a deterministic transition function,
  which maps its state and the messages delivered to a new state and a multiset of messages for
  its out-neighbours.
* `Protocol.lts`: the labelled transition system of a protocol, whose transitions apply the
  events (`Protocol.applyEvent`) whose messages are in transit.
* `Protocol.IsExecution`, `Protocol.IsInfiniteExecution`: finite and infinite executions, from
  an initial configuration (`Protocol.IsInitial`), as executions of `Protocol.lts` in CSLib's
  sense.
* `Protocol.IsLossyAdmissible`, `Protocol.IsAdmissible`: an infinite execution is admissible
  with lossy channels if every process takes infinitely many computation events, and admissible
  if, moreover, every message in transit is delivered later.

`Protocol.IsExecution.exists_isAdmissible_extension`: with finitely many processes, at least one,
every finite execution is the start of an admissible execution.

The tests in `CSLibExtTest` prove, for the client-server example of Aspnes's notes, that the
client receives the response in every admissible execution but not in every execution admissible
with lossy channels.

## References

* J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6, Chapter 2,
  Sections 2.1 and 2.2.
* S. Gilbert and N. Lynch, *Brewer's conjecture and the feasibility of consistent, available,
  partition-tolerant web services*, ACM SIGACT News 33(2), 2002, Sections 2.3 and 3.1.
-/

@[expose] public section

namespace Cslib.Distributed.AsyncMessagePassing

open Filter

variable {P Q M : Type*}

-- A configuration of processes `P` with states in `Q`, exchanging messages in `M`, gives the
-- state `state i` of every process `i` and, for every ordered pair of processes `i, j`, the
-- channel `chan i j`: the multiset of messages sent from `i` to `j` and not yet delivered.
@[ext]
structure Config (P Q M : Type*) where
  /-- The state of each process. -/
  state : P → Q
  /-- `chan i j` is the multiset of messages in transit from `i` to `j`. -/
  chan : P → P → Multiset M

-- In an event, the process `proc` receives the multiset `delivered` of messages, each paired
-- with its sender, and takes a step. It is a delivery event if it delivers at least one message,
-- and a computation event if `delivered` is empty.
@[ext]
structure Event (P M : Type*) where
  /-- The process that takes the step. -/
  proc : P
  /-- The messages delivered to it, each paired with its sender. -/
  delivered : Multiset (P × M)

/-- **Protocols of asynchronous message-passing systems.** A protocol for the processes `P` on the
directed network `G` gives each process `i` a set `init i` of initial states and a deterministic
transition function `trans i`. It maps a state of `i` and a multiset of messages delivered to `i`,
each paired with its sender, to a new state of `i` and a multiset of messages to send, each paired
with its recipient, which is an out-neighbour of `i` in `G`. -/
structure Protocol (G : Digraph P) (Q M : Type*) where
  /-- The initial states of each process. -/
  init : P → Set Q
  /-- The transition function of each process. -/
  trans : P → Q → Multiset (P × M) → Q × Multiset (P × M)
  /-- Every message is sent to an out-neighbour of its sender. -/
  adj_of_mem_trans : ∀ i q A x, x ∈ (trans i q A).2 → G.Adj i x.1

private theorem count_map_snd_filter_fst [DecidableEq P] [DecidableEq M] (A : Multiset (P × M))
    (i : P) (m : M) : ((A.filter (·.1 = i)).map Prod.snd).count m = A.count (i, m) := by
  rw [Multiset.count_map, Multiset.filter_filter, Multiset.count_eq_card_filter_eq]
  congr 1
  refine Multiset.filter_congr fun x _ => ?_
  obtain ⟨a, b⟩ := x
  constructor
  · rintro ⟨rfl, rfl⟩
    rfl
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩

namespace Protocol

variable {G : Digraph P}

/-- **Initial configurations of an asynchronous message-passing system.** A configuration is
initial for a protocol if every process is in one of its initial states and every channel is
empty. -/
def IsInitial (π : Protocol G Q M) (C : Config P Q M) : Prop :=
  (∀ i, C.state i ∈ π.init i) ∧ ∀ i j, C.chan i j = 0

variable [DecidableEq P] [DecidableEq M]

-- Applying an event `e` of process `p`, delivering the multiset `A` of messages paired with their
-- senders, to the configuration `C`: with `(q, B)` the value of the transition function of `p`
-- at its state in `C` and `A`, the event removes from each channel `chan i p` the messages of `A`
-- sent by `i`, sets the state of `p` to `q`, and adds to each channel `chan p j` the messages of
-- `B` for `j`.
def applyEvent (π : Protocol G Q M) (C : Config P Q M) (e : Event P M) : Config P Q M where
  state := Function.update C.state e.proc (π.trans e.proc (C.state e.proc) e.delivered).1
  chan i j :=
    C.chan i j - (if j = e.proc then (e.delivered.filter (·.1 = i)).map Prod.snd else 0) +
      if i = e.proc then
        ((π.trans e.proc (C.state e.proc) e.delivered).2.filter (·.1 = j)).map Prod.snd
      else 0

-- The transition system of a protocol: an event `e` of process `p` takes the configuration `C` to
-- `C'` if, for every process `i`, the messages it delivers from `i` form a sub-multiset of the
-- channel `chan i p` of `C`, and `C'` is the result of applying `e` to `C`.
def lts (π : Protocol G Q M) : LTS (Config P Q M) (Event P M) where
  Tr C e C' := (∀ i, (e.delivered.filter (·.1 = i)).map Prod.snd ≤ C.chan i e.proc) ∧
    C' = π.applyEvent C e

/-- **Finite executions of an asynchronous message-passing system.** `π.IsExecution C₀ φs C Cs`
says that the configurations `Cs = [C₀, C₁, …, Cₙ]`, with `Cₙ = C`, and the events
`φs = [φ₁, …, φₙ]` form an execution of `π`: `C₀` is initial, and each event `φₖ₊₁` can occur in
`Cₖ` and `Cₖ₊₁` results from applying it, as a transition of `π.lts`. An event of process `p` can
occur in a configuration if, for every process `i`, the messages it delivers from `i` are in the
channel `chan i p`, with multiplicity. Applying it removes them from these channels, gives `p` the
state its transition function assigns to its current state and the messages delivered, and adds
each message that the transition function sends to the channel from `p` to its recipient. -/
def IsExecution (π : Protocol G Q M) (C₀ : Config P Q M) (φs : List (Event P M))
    (C : Config P Q M) (Cs : List (Config P Q M)) : Prop :=
  π.IsInitial C₀ ∧ π.lts.Execution C₀ φs C Cs

/-- **Infinite executions of an asynchronous message-passing system.** The configurations `Cs`
and the events `φs` form an infinite execution of `π` if `Cs 0` is initial and, for every `n`, the
event `φs n` can occur in `Cs n` and `Cs (n + 1)` results from applying it, as a transition of
`π.lts`. An event of process `p` can occur in a configuration if, for every process `i`, the
messages it delivers from `i` are in the channel `chan i p`, with multiplicity. Applying it removes
them from these channels, gives `p` the state its transition function assigns to its current state
and the messages delivered, and adds each message that the transition function sends to the
channel from `p` to its recipient. -/
def IsInfiniteExecution (π : Protocol G Q M) (Cs : ωSequence (Config P Q M))
    (φs : ωSequence (Event P M)) : Prop :=
  π.IsInitial (Cs 0) ∧ π.lts.OmegaExecution Cs φs

/-- **Admissible executions with lossy channels.** An infinite execution of `π` is admissible with
lossy channels if every process takes infinitely many computation events, events of that process
that deliver no message. A message that is sent may never be delivered. -/
def IsLossyAdmissible (π : Protocol G Q M) (Cs : ωSequence (Config P Q M))
    (φs : ωSequence (Event P M)) : Prop :=
  π.IsInfiniteExecution Cs φs ∧ ∀ i, ∃ᶠ n in atTop, (φs n).proc = i ∧ (φs n).delivered = 0

/-- **Admissible executions of an asynchronous message-passing system.** With reliable channels,
an infinite execution of `π` is admissible if every process takes infinitely many computation
events, events of that process that deliver no message, and every message sent is eventually
delivered: whenever `m` is in the channel `chan i j` of `Cs n`, some event `φs k` with `n ≤ k` is
an event of `j` that delivers `m` from `i`. -/
def IsAdmissible (π : Protocol G Q M) (Cs : ωSequence (Config P Q M))
    (φs : ωSequence (Event P M)) : Prop :=
  π.IsLossyAdmissible Cs φs ∧
    ∀ n i j m, m ∈ (Cs n).chan i j → ∃ k, n ≤ k ∧ (φs k).proc = j ∧ (i, m) ∈ (φs k).delivered

theorem IsAdmissible.isLossyAdmissible {π : Protocol G Q M} {Cs : ωSequence (Config P Q M)}
    {φs : ωSequence (Event P M)} (h : π.IsAdmissible Cs φs) : π.IsLossyAdmissible Cs φs :=
  h.1

-- A computation event is enabled in every configuration.
theorem lts_tr_computation (π : Protocol G Q M) (C : Config P Q M) (i : P) :
    π.lts.Tr C ⟨i, 0⟩ (π.applyEvent C ⟨i, 0⟩) :=
  ⟨fun _ => by simpa only [Multiset.filter_zero, Multiset.map_zero] using Multiset.zero_le _, rfl⟩

-- A message in a channel stays there through a transition, unless the transition delivers it.
theorem mem_chan_of_lts_tr {π : Protocol G Q M} {C C' : Config P Q M} {e : Event P M}
    (h : π.lts.Tr C e C') {i j : P} {m : M} (hm : m ∈ C.chan i j) :
    m ∈ C'.chan i j ∨ e.proc = j ∧ (i, m) ∈ e.delivered := by
  obtain ⟨-, rfl⟩ := h
  by_cases hj : j = e.proc
  · by_cases hd : (i, m) ∈ e.delivered
    · exact Or.inr ⟨hj.symm, hd⟩
    · left
      refine Multiset.mem_of_le (Multiset.le_add_right _ _) ?_
      rw [← Multiset.count_pos, Multiset.count_sub, ite_eq_left hj, count_map_snd_filter_fst,
        Multiset.count_eq_zero.mpr hd, Nat.sub_zero, Multiset.count_pos]
      exact hm
  · left
    refine Multiset.mem_of_le (Multiset.le_add_right _ _) ?_
    simpa [hj] using hm

-- Channels that are not edges of the network stay empty through a transition.
theorem chan_eq_zero_of_lts_tr {π : Protocol G Q M} {C C' : Config P Q M} {e : Event P M}
    (h : π.lts.Tr C e C') (hC : ∀ i j, ¬G.Adj i j → C.chan i j = 0) :
    ∀ i j, ¬G.Adj i j → C'.chan i j = 0 := by
  obtain ⟨-, rfl⟩ := h
  intro i j hij
  simp only [applyEvent, hC i j hij, Multiset.zero_sub, zero_add]
  split_ifs with hi
  · subst hi
    rw [Multiset.map_eq_zero, Multiset.filter_eq_nil]
    rintro x hx rfl
    exact hij (π.adj_of_mem_trans _ _ _ x hx)
  · rfl

-- In a finite execution, only the edges of the network carry messages.
theorem IsExecution.chan_eq_zero_of_not_adj {π : Protocol G Q M} {C₀ C : Config P Q M}
    {φs : List (Event P M)} {Cs : List (Config P Q M)} (h : π.IsExecution C₀ φs C Cs)
    {i j : P} (hij : ¬G.Adj i j) : C.chan i j = 0 := by
  obtain ⟨hinit, hex⟩ := h
  suffices ∀ {D φs D' Ds}, π.lts.Execution D φs D' Ds →
      (∀ i j, ¬G.Adj i j → D.chan i j = 0) → ∀ i j, ¬G.Adj i j → D'.chan i j = 0 from
    this hex (fun i j _ => hinit.2 i j) i j hij
  intro D φs D' Ds hex hD
  induction hex with
  | refl => exact hD
  | stepL htr _ ih => exact ih (chan_eq_zero_of_lts_tr htr hD)

-- In an infinite execution, only the edges of the network carry messages.
theorem IsInfiniteExecution.chan_eq_zero_of_not_adj {π : Protocol G Q M}
    {Cs : ωSequence (Config P Q M)} {φs : ωSequence (Event P M)}
    (h : π.IsInfiniteExecution Cs φs) (n : ℕ) {i j : P} (hij : ¬G.Adj i j) :
    (Cs n).chan i j = 0 :=
  IsExecution.chan_eq_zero_of_not_adj ⟨h.1, h.2.extract_execution (Nat.zero_le n)⟩ hij

-- A message in a channel of an infinite execution stays there, unless it is delivered.
theorem mem_chan_or_delivered {π : Protocol G Q M} {Cs : ωSequence (Config P Q M)}
    {φs : ωSequence (Event P M)} (h : π.lts.OmegaExecution Cs φs) {n : ℕ} {i j : P} {m : M}
    (hm : m ∈ (Cs n).chan i j) (d : ℕ) :
    m ∈ (Cs (n + d)).chan i j ∨
      ∃ k, n ≤ k ∧ k < n + d ∧ (φs k).proc = j ∧ (i, m) ∈ (φs k).delivered := by
  induction d with
  | zero => exact Or.inl hm
  | succ d ih =>
    rcases ih with hd | ⟨k, hnk, hk, hkj, hkm⟩
    · rcases mem_chan_of_lts_tr (h (n + d)) hd with hd' | ⟨hj, hdel⟩
      · exact Or.inl hd'
      · exact Or.inr ⟨n + d, by omega, by omega, hj, hdel⟩
    · exact Or.inr ⟨k, hnk, by omega, hkj, hkm⟩

section Fair

variable [Fintype P]

/-- All messages in transit to `j`, each paired with its sender. -/
private def inTransitTo (C : Config P Q M) (j : P) : Multiset (P × M) :=
  ∑ i, (C.chan i j).map (Prod.mk i)

private theorem count_inTransitTo (C : Config P Q M) (i j : P) (m : M) :
    (inTransitTo C j).count (i, m) = (C.chan i j).count m := by
  rw [inTransitTo, Multiset.count_sum', Finset.sum_eq_single i]
  · exact Multiset.count_map_eq_count' _ _ (Prod.mk_right_injective i) m
  · intro i' _ hi'
    refine Multiset.count_eq_zero.mpr fun hmem => hi' ?_
    obtain ⟨m', -, hm'⟩ := Multiset.mem_map.mp hmem
    exact (Prod.ext_iff.mp hm').1
  · simp

omit [DecidableEq M] in
private theorem map_snd_filter_inTransitTo (C : Config P Q M) (i j : P) :
    ((inTransitTo C j).filter (·.1 = i)).map Prod.snd = C.chan i j := by
  classical
  ext m
  rw [count_map_snd_filter_fst, count_inTransitTo]

variable [Nonempty P]

omit [DecidableEq P] in
/-- A schedule of the processes that names each process infinitely often. -/
private noncomputable def sched (k : ℕ) : P :=
  (Fintype.equivFin P).symm ⟨k % Fintype.card P, Nat.mod_lt _ Fintype.card_pos⟩

omit [DecidableEq P] in
private theorem exists_sched_eq (i : P) (N : ℕ) : ∃ k, N ≤ k ∧ sched k = i := by
  have hpos : 0 < Fintype.card P := Fintype.card_pos
  refine ⟨Fintype.equivFin P i + N * Fintype.card P,
    Nat.le_add_left_of_le (Nat.le_mul_of_pos_right N hpos), ?_⟩
  rw [sched, Equiv.symm_apply_eq]
  ext
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fintype.equivFin P i).isLt]

/-- At even steps the scheduled process receives every message in transit to it; at odd steps
it takes a computation event. -/
private noncomputable def fairEvent (k : ℕ) (C : Config P Q M) : Event P M :=
  if k % 2 = 0 then ⟨sched (k / 2), inTransitTo C (sched (k / 2))⟩ else ⟨sched (k / 2), 0⟩

/-- The configurations of the fair continuation of `C`. -/
private noncomputable def fairConfig (π : Protocol G Q M) (C : Config P Q M) : ℕ → Config P Q M
  | 0 => C
  | k + 1 => π.applyEvent (fairConfig π C k) (fairEvent k (fairConfig π C k))

private theorem fairConfig_tr (π : Protocol G Q M) (C : Config P Q M) (k : ℕ) :
    π.lts.Tr (fairConfig π C k) (fairEvent k (fairConfig π C k)) (fairConfig π C (k + 1)) := by
  refine ⟨fun i => ?_, rfl⟩
  unfold fairEvent
  split_ifs
  · rw [map_snd_filter_inTransitTo]
  · simpa only [Multiset.filter_zero, Multiset.map_zero] using Multiset.zero_le _

end Fair

/-- From every configuration, some infinite sequence of transitions gives every process infinitely
many computation events and delivers every message in transit. -/
private theorem exists_fair_continuation [Finite P] [Nonempty P] (π : Protocol G Q M)
    (C : Config P Q M) :
    ∃ (Ds : ωSequence (Config P Q M)) (ψs : ωSequence (Event P M)), Ds 0 = C ∧
      π.lts.OmegaExecution Ds ψs ∧
      (∀ i, ∃ᶠ n in atTop, (ψs n).proc = i ∧ (ψs n).delivered = 0) ∧
      ∀ n i j m, m ∈ (Ds n).chan i j →
        ∃ k, n ≤ k ∧ (ψs k).proc = j ∧ (i, m) ∈ (ψs k).delivered := by
  have := Fintype.ofFinite P
  refine ⟨⟨fairConfig π C⟩, ⟨fun k => fairEvent k (fairConfig π C k)⟩, rfl,
    fun k => fairConfig_tr π C k, fun i => frequently_atTop.mpr fun N => ?_,
    fun n i j m hm => ?_⟩
  · obtain ⟨k, hNk, hk⟩ := exists_sched_eq i N
    refine ⟨2 * k + 1, by omega, ?_⟩
    change (fairEvent (2 * k + 1) _).proc = i ∧ (fairEvent (2 * k + 1) _).delivered = 0
    have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp only [fairEvent, ite_eq_right h1, h2, hk, and_self]
  · obtain ⟨k, hnk, hk⟩ := exists_sched_eq j n
    have hex : π.lts.OmegaExecution (⟨fairConfig π C⟩ : ωSequence (Config P Q M))
        ⟨fun k => fairEvent k (fairConfig π C k)⟩ := fun k => fairConfig_tr π C k
    rcases mem_chan_or_delivered hex hm (2 * k - n) with hmem | ⟨k', hnk', -, hk'⟩
    · refine ⟨2 * k, by omega, ?_⟩
      change (fairEvent (2 * k) _).proc = j ∧ (i, m) ∈ (fairEvent (2 * k) _).delivered
      have h1 : 2 * k % 2 = 0 := by omega
      have h2 : 2 * k / 2 = k := by omega
      have hk2 : n + (2 * k - n) = 2 * k := by omega
      rw [hk2] at hmem
      simp only [fairEvent, ite_eq_left h1, h2, hk, true_and]
      rw [← Multiset.count_pos, count_inTransitTo, Multiset.count_pos]
      exact hmem
    · exact ⟨k', hnk', hk'⟩

/-- **Every finite execution extends to an admissible execution.** For a protocol with finitely
many processes, at least one, every finite execution, with configurations `Cs` and events `φs`, is
the start of an admissible execution: for some continuations `Ds` and `ψs`, the configurations
`Cs ++ω Ds` and the events `φs ++ω ψs` form an admissible execution. -/
theorem IsExecution.exists_isAdmissible_extension [Finite P] [Nonempty P]
    {π : Protocol G Q M} {C₀ C : Config P Q M} {φs : List (Event P M)}
    {Cs : List (Config P Q M)} (h : π.IsExecution C₀ φs C Cs) :
    ∃ (Ds : ωSequence (Config P Q M)) (ψs : ωSequence (Event P M)),
      π.IsAdmissible (Cs ++ω Ds) (φs ++ω ψs) := by
  obtain ⟨hinit, hex⟩ := h
  obtain ⟨Es, ψs, hE0, hEex, hEcomp, hEdel⟩ := exists_fair_continuation π C
  have hlen : Cs.length = φs.length + 1 := hex.length
  -- The configurations of the glued execution from position `φs.length` on are those of `Es`.
  have hshift : ∀ d, (Cs ++ω Es.tail) (φs.length + d) = Es d := by
    intro d
    rcases d with _ | d
    · rw [Nat.add_zero, ωSequence.get_append_left _ _ _ (by omega), hE0]
      exact hex.last'
    · rw [show φs.length + (d + 1) = Cs.length + d by omega, ωSequence.get_append_right]
      rfl
  have hshiftφ : ∀ d, (φs ++ω ψs) (φs.length + d) = ψs d := fun d =>
    ωSequence.get_append_right _ _ _
  have hglue : π.lts.OmegaExecution (Cs ++ω Es.tail) (φs ++ω ψs) :=
    LTS.OmegaExecution.prepend_execution hex hEex hE0
  refine ⟨Es.tail, ψs, ⟨⟨?_, hglue⟩, fun i => ?_⟩, fun n i j m hm => ?_⟩
  · rw [ωSequence.get_append_left _ _ _ (by omega), hex.start]
    exact hinit
  · refine frequently_atTop.mpr fun N => ?_
    obtain ⟨k, hNk, hk⟩ := frequently_atTop.mp (hEcomp i) N
    exact ⟨φs.length + k, by omega, by rwa [hshiftφ]⟩
  · by_cases hn : φs.length ≤ n
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [hshift] at hm
      obtain ⟨k, hdk, hk⟩ := hEdel d i j m hm
      exact ⟨φs.length + k, by omega, by rwa [hshiftφ]⟩
    · rcases mem_chan_or_delivered hglue hm (φs.length - n) with hmem | ⟨k, hnk, -, hk⟩
      · rw [show n + (φs.length - n) = φs.length + 0 by omega, hshift] at hmem
        obtain ⟨k, -, hk⟩ := hEdel 0 i j m hmem
        exact ⟨φs.length + k, by omega, by rwa [hshiftφ]⟩
      · exact ⟨k, hnk, hk⟩

end Protocol

end Cslib.Distributed.AsyncMessagePassing
