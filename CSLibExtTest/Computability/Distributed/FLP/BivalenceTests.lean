/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.FLP.Bivalence
public import Mathlib.Tactic.FinCases

/-!
# Tests for valence, bivalence and commutativity in CSLib's FLP model

The toy algorithm `adopt` on two processes: a process decides its input bit when it receives
it, and sends nothing. It is not a consensus algorithm (agreement fails), but it shows that the
notions are not vacuous:

* from the initial state with inputs `false, true` both values are reachable (bivalent);
* from the initial state with inputs `false, false` the value `true` is not reachable;
* the two input messages, which go to different processes, commute (`mTr_comm`);
* `adopt` satisfies the hypotheses of `exists_bivalent_start` (both values decidable, and a
  decision reachable without any one process), so they are jointly satisfiable. The proof is the
  reviewer's probe from the review of this change set.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.FLP.Tests

open Cslib.FLP

/-- Each process decides the input bit it receives and sends nothing. -/
def adopt : Algorithm (Fin 2) Unit Unit where
  init _ := ()
  next _ _ := ()
  send _ _ := 0
  out m _ := match m.msg with
    | .inl b => some b
    | .inr _ => none

/-- The input message of process `p` with input `b`. -/
def inMsg (p : Fin 2) (b : Bool) : Message (Fin 2) Unit := ⟨p, .inl b⟩

/-- The input messages are in flight in the initial state. -/
theorem inMsg_mem (inp : Fin 2 → Bool) (p : Fin 2) :
    inMsg p (inp p) ∈ (adopt.start inp).msgs := by
  fin_cases p <;> simp [Algorithm.start, inMsg]

/-- Receiving its input makes process `p` decide it. -/
theorem valent_start (inp : Fin 2 → Bool) (p : Fin 2) :
    Valent adopt (adopt.start inp) (inp p) := by
  refine ⟨adopt.recvMsg (inMsg p (inp p)) (adopt.start inp),
    ⟨[some (inMsg p (inp p))], LTS.MTr.single (lts := adopt.lts) ⟨inMsg_mem inp p, rfl⟩⟩,
    ⟨p, ?_⟩⟩
  simp [State.ProcDecided, Algorithm.recvMsg, Algorithm.start, adopt, inMsg]

/-- With inputs `false, true` both values are reachable. -/
example : Bivalent adopt (adopt.start (fun p : Fin 2 => decide (p = 1))) :=
  ⟨valent_start (fun p : Fin 2 => decide (p = 1)) 0, valent_start (fun p : Fin 2 => decide (p = 1)) 1⟩

/-- With all inputs `false`, every reachable state has decided only `false` and has only
messages carrying `false` in flight. -/
def AllFalse (s : State (Fin 2) Unit Unit) : Prop :=
  (∀ p b, s.ProcDecided p b → b = false) ∧ ∀ m ∈ s.msgs, m.msg = .inl false

/-- `AllFalse` is preserved by every step. -/
theorem allFalse_inv : adopt.lts.TrInv AllFalse := by
  intro s x s' htr hs
  cases x with
  | none => exact (Algorithm.tr_none htr) ▸ hs
  | some m =>
      obtain ⟨hm, rfl⟩ := htr
      have hmf := hs.2 m hm
      refine ⟨fun p b h => ?_, fun m' hm' => ?_⟩
      · simp only [State.ProcDecided, Algorithm.recvMsg] at h
        split_ifs at h with hp hn
        · have ho : adopt.out m (s.proc m.dest) = some false := by simp [adopt, hmf]
          simp only [ho, Option.some.injEq] at h
          exact h.symm
        · exact hs.1 _ _ h
        · exact hs.1 _ _ h
      · simp only [Algorithm.recvMsg, adopt, add_zero] at hm'
        exact hs.2 m' (Multiset.mem_of_mem_erase hm')

/-- With inputs `false, false` the value `true` is not reachable: not every state is
bivalent. -/
example : ¬ Valent adopt (adopt.start (fun _ : Fin 2 => false)) true := by
  rintro ⟨s, ⟨xs, h⟩, p, hp⟩
  have h0 : AllFalse (adopt.start (fun _ : Fin 2 => false)) := by
    refine ⟨fun p b h => by simp [State.ProcDecided, Algorithm.start] at h, fun m hm => ?_⟩
    simp only [Algorithm.start, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hm
    obtain ⟨q, rfl⟩ := hm
    fin_cases q <;> rfl
  exact absurd ((LTS.mtrInv_of_trInv allFalse_inv) _ _ _ h h0).1 (fun h' => by
    simpa using h' p true hp)

/-- The input messages of the two processes commute (`mTr_comm` with `ps = {0}`). -/
example (inp : Fin 2 → Bool) :
    ∃ s', adopt.lts.MTr (adopt.recvMsg (inMsg 0 (inp 0)) (adopt.start inp))
        [some (inMsg 1 (inp 1))] s' ∧
      adopt.lts.MTr (adopt.recvMsg (inMsg 1 (inp 1)) (adopt.start inp))
        [some (inMsg 0 (inp 0))] s' :=
  mTr_comm (ps := {0}) (by simp [DestIn, inMsg]) (LTS.MTr.single (lts := adopt.lts) ⟨inMsg_mem inp 0, rfl⟩)
    (by simp [DestIn, inMsg]) (LTS.MTr.single (lts := adopt.lts) ⟨inMsg_mem inp 1, rfl⟩)

/-- An algorithm solving consensus with one fault satisfies the termination hypothesis of the
bivalence lemmas (vacuously, by the impossibility theorem). -/
example {M S : Type} [DecidableEq M] (a : Algorithm (Fin 2) M S) (h : a.Consensus 1) :
    a.PseudoTermination 1 :=
  (PseudoConsensus.of_consensus 1 (by simp) h).2

/-- An invariant of `adopt`: in-flight messages carry their destination's input, and a process
that has not decided still has its input in flight. -/
def AdoptInv (inp : Fin 2 → Bool) (s : State (Fin 2) Unit Unit) : Prop :=
  (∀ m ∈ s.msgs, m.msg = .inl (inp m.dest)) ∧
    ∀ p, (s.proc p).out ≠ none ∨ (⟨p, .inl (inp p)⟩ : Message (Fin 2) Unit) ∈ s.msgs

theorem adoptInv_reachable {inp : Fin 2 → Bool} {s : State (Fin 2) Unit Unit}
    (hs : adopt.Reachable inp s) : AdoptInv inp s := by
  obtain ⟨xs, h⟩ := hs
  have inv : adopt.lts.TrInv (AdoptInv inp) := by
    intro s x s' htr hs
    cases x with
    | none => exact (Algorithm.tr_none htr) ▸ hs
    | some m =>
        obtain ⟨hm, rfl⟩ := htr
        obtain ⟨h1, h2⟩ := hs
        have hmm := h1 m hm
        refine ⟨fun m' hm' => ?_, fun p => ?_⟩
        · simp only [Algorithm.recvMsg, adopt, Multiset.add_zero] at hm'
          exact h1 m' (Multiset.mem_of_mem_erase hm')
        · by_cases hp : p = m.dest
          · left
            subst hp
            simp only [Algorithm.recvMsg, ite_true]
            split_ifs with hn
            · simp [adopt, hmm]
            · simpa using hn
          · rcases h2 p with h | h
            · left; simpa [Algorithm.recvMsg, hp] using h
            · right
              simp only [Algorithm.recvMsg, adopt, Multiset.add_zero]
              exact (Multiset.mem_erase_of_ne (by intro e; exact hp (by rw [← e]))).2 h
  refine LTS.mtrInv_of_trInv inv _ _ _ h ?_
  refine ⟨fun m hm => ?_, fun p => Or.inr ?_⟩
  · simp only [Algorithm.start, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hm
    obtain ⟨q, rfl⟩ := hm
    rfl
  · fin_cases p <;> simp [Algorithm.start]

/-- `adopt` reaches a decision from every reachable state without any one process. -/
theorem adopt_pseudoTermination : adopt.PseudoTermination 1 := by
  intro inp s hs ps hps
  obtain ⟨p, hp⟩ : ps.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite ps)]
    simp at hps
    omega
  by_cases hn : (s.proc p).out = none
  · have h : (⟨p, .inl (inp p)⟩ : Message (Fin 2) Unit) ∈ s.msgs :=
      ((adoptInv_reachable hs).2 p).resolve_left (by simp [hn])
    refine ⟨adopt.recvMsg ⟨p, .inl (inp p)⟩ s, inp p,
      Relation.ReflTransGen.single ⟨some ⟨p, .inl (inp p)⟩, hp, h, rfl⟩, p, ?_⟩
    simp [State.ProcDecided, Algorithm.recvMsg, hn, adopt]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hn
    exact ⟨s, b, Relation.ReflTransGen.refl, p, hb⟩

/-- Each value is decided in some reachable state of `adopt`. -/
theorem adopt_val (b : Bool) : ∃ inp s, adopt.Reachable inp s ∧ s.Decided b := by
  let m : Message (Fin 2) Unit := ⟨0, .inl b⟩
  have hm : m ∈ (adopt.start fun _ => b).msgs := by simp [Algorithm.start, m]
  refine ⟨fun _ => b, adopt.recvMsg m (adopt.start fun _ => b),
    ⟨[some m], LTS.MTr.single (lts := adopt.lts) ⟨hm, rfl⟩⟩, 0, ?_⟩
  simp [State.ProcDecided, Algorithm.recvMsg, Algorithm.start, adopt, m]

/-- Non-vacuity of Lemma 2: its hypotheses hold for `adopt`, which has a bivalent initial
state. -/
example : ∃ inp, Bivalent adopt (adopt.start inp) :=
  exists_bivalent_start adopt_val adopt_pseudoTermination

/-- The impossibility theorem, for two processes and one fault. -/
example {M S : Type} [DecidableEq M] : ¬ ∃ a : Algorithm (Fin 2) M S, a.Consensus 1 :=
  flp_impossibility (by simp) le_rfl

end Cslib.Distributed.FLP.Tests
