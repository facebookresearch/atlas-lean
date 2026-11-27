/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLP impossibility: commutativity, bivalence and the main theorem
-/
module

public import Cslib.Computability.Distributed.FLP.Impossibility

/-!
# The FLP impossibility theorem: commutativity and a bivalent initial state

Pinned CSLib proves the impossibility theorem of Fischer, Lynch and Paterson
(`Cslib.FLP.Consensus.ge_one_not_exists`) following Völzer's constructive proof, in its own
model of asynchronous message passing (`Cslib.FLP.Algorithm`). This file states that theorem
for the graph and proves, in the same model, the three lemmas of the original bivalence proof:
the commutativity of schedules run by disjoint sets of processes (Lemma 1 of Fischer, Lynch and
Paterson), the existence of a bivalent initial state (their Lemma 2), and the survival of
bivalence when any pending event is applied after a suitable delay (their Lemma 3).

Fischer, Lynch and Paterson prove their lemmas inside a proof by contradiction, under the
assumption that the protocol is totally correct in spite of one fault. Stated with CSLib's
`Consensus 1` as hypothesis they would be vacuous, since by the theorem no such algorithm exists
when there are at least two processes. They are therefore stated under the hypotheses their
proofs use: partial correctness (agreement for Lemma 3, both values decidable for Lemma 2) and
CSLib's `PseudoTermination 1` (a decision reachable from every reachable state without any one
process), which follows from the contradiction hypothesis
(`CSLibExt.Computability.Distributed.FLP.Original`). The hypotheses of Lemma 2 are jointly
satisfiable: the test module checks them for an algorithm on two processes. By an informal
argument, those of Lemma 3 cannot all hold with exactly two processes and a reachable bivalent
state: by Lemma 1 and agreement, the solo runs of either process from a state decide one common
value, which no step changes. For three or more processes a Paxos-type algorithm satisfies
them, but no such algorithm is formalized here, so the non-vacuity of Lemma 3 is not checked in
Lean.

## Model (CSLib's `Cslib.FLP.Algorithm`)

* **Synchrony:** none. There are no clocks and no bounds on relative speeds or message delays;
  a step is the receipt of one in-flight message, chosen by the scheduler, and the stuttering
  step changes nothing.
* **Failures:** crash. In an infinite run a process is faulty if from some time on a message to
  it is in flight but it receives nothing more; at most `f` processes are faulty.
* **Communication:** a reliable asynchronous message buffer (a multiset: unordered, no loss,
  no duplication, no corruption). A fair run delivers every message to a process that is not
  faulty. Each process's input bit is a message to it that is in flight in the initial state;
  it may be received after other messages.
* **Protocols:** deterministic; a process's step depends on its state and the message it
  receives; decisions are write-once.
* **Consensus** (`Cslib.FLP.Algorithm.Consensus`): in every reachable state the decided values
  agree and each is the input of some process, and in every admissible run every process that
  is not faulty decides.

This correctness condition is stronger than the one in the theorem of Fischer, Lynch and
Paterson, who require only that some process decides in every admissible run and that both
decision values are reachable. The CSLib theorem is therefore weaker than their Theorem 1; the
original statement is proved in `CSLibExt.Computability.Distributed.FLP.Original` from the lemmas
of this file.

## Main definitions

* `Valent a s b`: some state reachable from `s` has decided `b`.
* `Bivalent a s`: both values are reachable from `s`.
* `ReachWithout a m s t`: `t` is reachable from `s` without receiving `m`.

## Main results

* `flp_impossibility`: CSLib's FLP theorem, restated: with at least two processes no algorithm
  solves consensus tolerating `f ≥ 1` crash faults.
* `mTr_comm`: Lemma 1 of Fischer, Lynch and Paterson in CSLib's model. Two schedules whose
  receiving processes are disjoint can be run in either order from a common state and lead to
  the same state.
* `exists_bivalent_start`: Lemma 2 of Fischer, Lynch and Paterson in CSLib's model. If both
  values can be decided and a decision is always reachable without any one process, some initial
  state is bivalent.
* `exists_bivalent_recvMsg`: Lemma 3 of Fischer, Lynch and Paterson in CSLib's model. From a
  bivalent reachable state and a message `m` in flight, some state reachable without receiving
  `m` leads, on receiving `m`, to a bivalent state.

## References

* M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one
  faulty process*, Journal of the ACM 32(2), 1985, 374–382: Lemmas 1–3, Theorem 1.
* H. Völzer, *A constructive proof for FLP*, Information Processing Letters 92(2), 2004,
  83–87 (the proof formalized in CSLib).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.FLP

open Cslib.FLP Function Set Fintype

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- **FLP impossibility of asynchronous consensus (CSLib form)** (Fischer, Lynch and Paterson,
1985, Theorem 1, in the form proved in CSLib after Völzer, 2004). With at least two processes,
no deterministic asynchronous message-passing algorithm solves consensus tolerating `f ≥ 1`
crash faults, where solving consensus means agreement, validity (a decided value is some
input) and termination of every process that is not faulty in every admissible run. -/
theorem flp_impossibility [Fintype P] {f : ℕ} (hP : 2 ≤ card P) (hf : 1 ≤ f) :
    ¬ ∃ a : Algorithm P M S, a.Consensus f :=
  Consensus.ge_one_not_exists hP hf

/-- **Valence of a state.** `Valent a s b` holds when some state reachable from `s` by the
algorithm `a` has decided `b` (Fischer, Lynch and Paterson, 1985, §3: `b` belongs to the set of
decision values of the configurations reachable from `s`). -/
def Valent (a : Algorithm P M S) (s : State P M S) (b : Bool) : Prop :=
  ∃ s', a.lts.CanReach s s' ∧ s'.Decided b

/-- **Bivalent state.** Both decision values are reachable from `s` (Fischer, Lynch and
Paterson, 1985, §3). -/
def Bivalent (a : Algorithm P M S) (s : State P M S) : Prop :=
  Valent a s false ∧ Valent a s true

/-! ### Lemma 1: commutativity of disjoint schedules -/

section Commute

variable {a : Algorithm P M S}

/-- One step against a schedule with disjoint receivers. -/
private theorem tr_mTr_comm {ps : Set P} {x : Action P M} {xs : List (Action P M)}
    {s s1 s2 : State P M S} (hx : DestIn ps x) (h1 : a.lts.Tr s x s1)
    (hxs : xs.Forall (DestIn psᶜ)) (h2 : a.lts.MTr s xs s2) :
    ∃ s', a.lts.MTr s1 xs s' ∧ a.lts.Tr s2 x s' := by
  induction h2 generalizing s1 with
  | refl => exact ⟨s1, .refl, h1⟩
  | stepL htr _ ih =>
      obtain ⟨hy, hxs⟩ := (List.forall_cons _ _ _).1 hxs
      obtain ⟨t, ht1, ht2⟩ := Algorithm.tr_diamond hx h1 hy htr
      obtain ⟨s', hs', hs2⟩ := ih ht2 hxs
      exact ⟨s', .stepL ht1 hs', hs2⟩

/-- **Commutativity of disjoint schedules** (Fischer, Lynch and Paterson, 1985, Lemma 1, in
CSLib's model). If from a state `s` the schedule `xs₁` leads to `s₁` and the schedule `xs₂`
leads to `s₂`, and every message received in `xs₁` goes to a process of `ps` while every
message received in `xs₂` goes to a process outside `ps`, then `xs₂` can be applied to `s₁`
and `xs₁` to `s₂`, and both lead to the same state. -/
theorem mTr_comm {ps : Set P} {xs₁ xs₂ : List (Action P M)} {s s₁ s₂ : State P M S}
    (hx₁ : xs₁.Forall (DestIn ps)) (h₁ : a.lts.MTr s xs₁ s₁)
    (hx₂ : xs₂.Forall (DestIn psᶜ)) (h₂ : a.lts.MTr s xs₂ s₂) :
    ∃ s', a.lts.MTr s₁ xs₂ s' ∧ a.lts.MTr s₂ xs₁ s' := by
  induction h₁ generalizing s₂ with
  | refl => exact ⟨s₂, h₂, .refl⟩
  | stepL htr _ ih =>
      obtain ⟨hx, hx₁⟩ := (List.forall_cons _ _ _).1 hx₁
      obtain ⟨t, ht, ht₂⟩ := tr_mTr_comm hx htr hx₂ h₂
      obtain ⟨s', hs', hs₂⟩ := ih hx₁ ht
      exact ⟨s', hs', .stepL ht₂ hs₂⟩

end Commute

/-! ### Lemma 2: a bivalent initial state -/

section Bivalent

variable {a : Algorithm P M S}

omit [DecidableEq P] [DecidableEq M] in
/-- Whether a state has decided a value depends only on the local states of the processes. -/
private theorem decided_of_proc_eq {s t : State P M S} (h : s.proc = t.proc) {b : Bool}
    (hs : s.Decided b) : t.Decided b := by
  obtain ⟨p, hp⟩ := hs
  exact ⟨p, by simpa [State.ProcDecided, ← h] using hp⟩

/-- If the inputs `inp₁` and `inp₂` agree outside `p` and `b` can be decided from the initial
state of `inp₁` without the participation of `p`, then `b` is reachable from the initial state
of `inp₂`. -/
private theorem valent_of_canDecideWithout [Fintype P] {inp₁ inp₂ : P → Bool} {p : P}
    {b : Bool} (he : EqOn inp₁ inp₂ {p}ᶜ) (h : a.CanDecideWithout (a.start inp₁) p b) :
    Valent a (a.start inp₂) b := by
  obtain ⟨s₁, hr, hd⟩ := h
  obtain ⟨s₂, hr₂, hp⟩ := CanReachVia.subset_inp he hr
  exact ⟨s₂, CanReachVia.canReach hr₂, decided_of_proc_eq hp.symm hd⟩

/-- From every reachable state a decision can be reached without any given process. -/
private theorem canDecideWithout_of_pseudoTermination [Fintype P] (hpt : a.PseudoTermination 1)
    {inp : P → Bool} {s : State P M S} (hr : a.Reachable inp s) (p : P) :
    ∃ b, a.CanDecideWithout s p b := by
  obtain ⟨s', b, hs', hd⟩ := hpt inp s hr {p}ᶜ (by simp [Set.ncard_compl {p}])
  exact ⟨b, s', hs', hd⟩

/-- **A bivalent initial state** (Fischer, Lynch and Paterson, 1985, Lemma 2, in CSLib's
model). Let `a` be partially correct (each value is decided in some reachable state; agreement is
not needed for this lemma) and satisfy
`PseudoTermination 1`: from every reachable state a decision can be reached without the
participation of any one process. Then some input assignment has a bivalent initial state: from
it both decision values are reachable. -/
theorem exists_bivalent_start [Fintype P]
    (hval : ∀ b, ∃ inp s, a.Reachable inp s ∧ s.Decided b) (hpt : a.PseudoTermination 1) :
    ∃ inp, Bivalent a (a.start inp) := by
  -- Every initial state can reach a decision without any given process.
  have hex : ∀ inp p, ∃ b, a.CanDecideWithout (a.start inp) p b := fun inp p =>
    canDecideWithout_of_pseudoTermination hpt (Algorithm.reachable_start (a := a)) p
  -- Initial states from which `false` and `true` are reachable.
  obtain ⟨inp₀, s₀, hs₀, hd₀⟩ := hval false
  obtain ⟨inp₁, s₁, hs₁, hd₁⟩ := hval true
  -- The inputs `inp k`: the first `k` processes in some numbering have their `inp₁` input,
  -- the others their `inp₀` input.
  let e := equivFin P
  let inp : ℕ → P → Bool := fun k q => if (e q).val < k then inp₁ q else inp₀ q
  have e₀ : inp 0 = inp₀ := by funext q; simp [inp]
  have e₁ : inp (card P) = inp₁ := by funext q; simp [inp, (e q).isLt]
  have h0 : Valent a (a.start (inp 0)) false := e₀ ▸ ⟨s₀, hs₀, hd₀⟩
  have hn : Valent a (a.start (inp (card P))) true := e₁ ▸ ⟨s₁, hs₁, hd₁⟩
  -- Otherwise `false` would stay reachable from `inp k` for every `k`, up to `card P`.
  by_contra hno
  have key : ∀ k, k ≤ card P → Valent a (a.start (inp k)) false := by
    intro k
    induction k with
    | zero => exact fun _ => h0
    | succ k ih =>
        intro hk
        have hv := ih (by omega)
        -- The inputs `inp k` and `inp (k + 1)` differ only at the process `p` numbered `k`.
        let p := e.symm ⟨k, by omega⟩
        have he : EqOn (inp k) (inp (k + 1)) {p}ᶜ := by
          intro q hq
          have hq' : (e q).val ≠ k := fun h => hq (by
            rw [Set.mem_singleton_iff]
            apply e.injective
            simp [p, Fin.ext_iff, h])
          simp only [inp]
          congr 1
          exact propext (by omega)
        obtain ⟨b, hb⟩ := hex (inp k) p
        cases b
        · exact valent_of_canDecideWithout he hb
        · exact absurd ⟨inp k, hv, valent_of_canDecideWithout (fun _ _ => rfl) hb⟩ hno
  exact hno ⟨inp (card P), key _ le_rfl, hn⟩

/-! ### Lemma 3: a bivalent state survives any pending event -/

omit [DecidableEq P] [DecidableEq M] in
/-- Split a list at the first occurrence of an element. -/
private theorem exists_first_split {β : Type*} {x : β} {l : List β} (h : x ∈ l) :
    ∃ ys zs, l = ys ++ x :: zs ∧ x ∉ ys := by
  classical
  induction l with
  | nil => simp at h
  | cons y l ih =>
      by_cases hy : y = x
      · exact ⟨[], l, by simp [hy], by simp⟩
      · obtain ⟨ys, zs, rfl, hys⟩ := ih (by simpa [Ne.symm hy, eq_comm] using h)
        exact ⟨y :: ys, zs, rfl, by simp [Ne.symm hy, hys]⟩

/-- Reachability is transitive. -/
private theorem canReach_trans {s t u : State P M S} (h₁ : a.lts.CanReach s t)
    (h₂ : a.lts.CanReach t u) : a.lts.CanReach s u := by
  obtain ⟨xs, hxs⟩ := h₁
  obtain ⟨ys, hys⟩ := h₂
  exact ⟨xs ++ ys, LTS.MTr.comp _ hxs hys⟩

/-- A value reachable from a later state is reachable from an earlier one. -/
private theorem valent_of_canReach {s t : State P M S} {b : Bool} (h : a.lts.CanReach s t)
    (ht : Valent a t b) : Valent a s b := by
  obtain ⟨u, hu, hd⟩ := ht
  exact ⟨u, canReach_trans h hu, hd⟩

/-- One step is a reachability. -/
private theorem canReach_of_tr {s t : State P M S} {x : Action P M} (h : a.lts.Tr s x t) :
    a.lts.CanReach s t :=
  ⟨[x], LTS.MTr.single _ h⟩

/-- **Reachability without an event.** `ReachWithout a m s t` holds when `t` is reachable from
`s` by a schedule that never receives the message `m` (Fischer, Lynch and Paterson, 1985,
Lemma 3: `t` belongs to the set `𝒞` of configurations reachable from `s` without applying the
event `e = (p, m)`). -/
def ReachWithout (a : Algorithm P M S) (m : Message P M) (s t : State P M S) : Prop :=
  ∃ xs, a.lts.MTr s xs t ∧ some m ∉ xs

/-- Walking along a schedule that avoids `m`, from a state where `D` has no value `c` to one where
it has `c`, finds one step where `c` appears. -/
private theorem exists_step_flip (m : Message P M) (D : State P M S → State P M S) (c : Bool)
    {g t : State P M S} {xs : List (Action P M)} (h : a.lts.MTr g xs t) (hxs : some m ∉ xs)
    (hg : ¬ Valent a (D g) c) (ht : Valent a (D t) c) :
    ∃ g₁ x g₂, ReachWithout a m g g₁ ∧ x ≠ some m ∧ a.lts.Tr g₁ x g₂ ∧
      ¬ Valent a (D g₁) c ∧ Valent a (D g₂) c := by
  induction h with
  | refl => exact absurd ht hg
  | @stepL g x g' ys t htr _ ih =>
      have hx : x ≠ some m := fun e => hxs (e ▸ List.mem_cons_self ..)
      by_cases hg' : Valent a (D g') c
      · exact ⟨g, x, g', ⟨[], .refl, by simp⟩, hx, htr, hg, hg'⟩
      · obtain ⟨g₁, y, g₂, ⟨zs, h₁, hzs⟩, hy, h₂, h₃, h₄⟩ :=
          ih (fun e => hxs (List.mem_cons_of_mem _ e)) hg' ht
        refine ⟨g₁, y, g₂, ⟨x :: zs, .stepL htr h₁, ?_⟩, hy, h₂, h₃, h₄⟩
        simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hx, hzs⟩

/-- **A bivalent configuration survives any pending event** (Fischer, Lynch and Paterson,
1985, Lemma 3, in CSLib's model). Let there be at least two processes, and let `a` satisfy
agreement (no reachable state has decided two values) and `PseudoTermination 1` (from every
reachable state a decision can be reached without the participation of any one process). If a
reachable state `s` is bivalent and the message `m` is in flight in `s`, then some state `t`
reachable from `s` without receiving `m` still has `m` in flight, and receiving `m` in `t` leads
to a bivalent state. -/
theorem exists_bivalent_recvMsg [Fintype P] (hP : 2 ≤ card P)
    (hag : ∀ inp s, a.Reachable inp s → s.Agreed) (hpt : a.PseudoTermination 1)
    {inp : P → Bool} {s : State P M S} (hr : a.Reachable inp s) (hb : Bivalent a s)
    {m : Message P M} (hm : m ∈ s.msgs) :
    ∃ t, ReachWithout a m s t ∧ m ∈ t.msgs ∧ Bivalent a (a.recvMsg m t) := by
  -- Every reachable state has a value.
  have hval : ∀ u, a.Reachable inp u → ∃ b, Valent a u b := by
    intro u hu
    obtain ⟨q⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨b, v, hv, hd⟩ := canDecideWithout_of_pseudoTermination hpt hu q
    exact ⟨b, v, CanReachVia.canReach hv, hd⟩
  -- A decided reachable state has only its decided value.
  have hdec : ∀ u b c, a.Reachable inp u → u.Decided b → Valent a u c → b = c := by
    intro u b c hu hd ⟨v, hv, hdv⟩
    exact (hag inp v (Algorithm.reachable_stable hu hv)) b c
      ⟨Algorithm.decided_stable hd hv, hdv⟩
  -- The message `m` stays in flight, and the states of `𝒞` are reachable.
  have hmem : ∀ t, ReachWithout a m s t → m ∈ t.msgs := fun t ⟨xs, h, hxs⟩ =>
    Algorithm.mTr_notRcvd_enabled h hm hxs
  have hreach : ∀ t, ReachWithout a m s t → a.Reachable inp t := fun t ⟨xs, h, _⟩ =>
    Algorithm.reachable_stable hr ⟨xs, h⟩
  have hDreach : ∀ t, ReachWithout a m s t → a.Reachable inp (a.recvMsg m t) := fun t ht =>
    Algorithm.reachable_stable (hreach t ht) (canReach_of_tr (x := some m) ⟨hmem t ht, rfl⟩)
  by_contra hno
  push Not at hno
  -- So every state of `𝒟 = e(𝒞)` is univalent.
  have huni : ∀ t, ReachWithout a m s t → ∀ c, Valent a (a.recvMsg m t) c →
      ¬ Valent a (a.recvMsg m t) (!c) := by
    intro t ht c hc hc'
    refine hno t ht (hmem t ht) ?_
    cases c
    · exact ⟨hc, hc'⟩
    · exact ⟨hc', hc⟩
  -- Both values occur in `𝒟`.
  have hboth : ∀ c, ∃ t, ReachWithout a m s t ∧ Valent a (a.recvMsg m t) c := by
    intro c
    have hc : Valent a s c := by cases c; exacts [hb.1, hb.2]
    obtain ⟨E, ⟨xs, hxs⟩, hE⟩ := hc
    by_cases hin : some m ∈ xs
    · -- Split at the first receipt of `m`.
      obtain ⟨ys, zs, rfl, hys⟩ := exists_first_split hin
      obtain ⟨E', hE', hrest⟩ := LTS.MTr.split hxs
      obtain ⟨F, hF, hrest'⟩ := LTS.MTr.cons_iff.1 hrest
      obtain ⟨-, rfl⟩ := hF
      exact ⟨E', ⟨ys, hE', hys⟩, E, ⟨zs, hrest'⟩, hE⟩
    · refine ⟨E, ⟨xs, hxs, hin⟩, a.recvMsg m E, LTS.CanReach.refl _ _, ?_⟩
      exact Algorithm.decided_stable hE (canReach_of_tr (x := some m)
        ⟨hmem E ⟨xs, hxs, hin⟩, rfl⟩)
  -- The value `b₀` of `e(s)`, and a state of `𝒞` whose image has the other value.
  have hs₀ : ReachWithout a m s s := ⟨[], .refl, by simp⟩
  obtain ⟨b₀, hb₀⟩ := hval _ (hDreach s hs₀)
  obtain ⟨t, ⟨xs, hxs, hxsm⟩, ht⟩ := hboth (!b₀)
  -- Neighbours `g₁ → g₂` in `𝒞` whose images have different values.
  obtain ⟨g₁, x, g₂, hg₁C, hx, htr, h₁, h₂⟩ := exists_step_flip m (a.recvMsg m) (!b₀) hxs hxsm
    (huni s hs₀ b₀ hb₀) ht
  have hg₂C : ReachWithout a m s g₂ := by
    obtain ⟨ys, hys, hysm⟩ := hg₁C
    refine ⟨ys ++ [x], LTS.MTr.stepR _ hys htr, ?_⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hysm, Ne.symm hx⟩
  -- The other value of a reachable state.
  have hother : ∀ u, a.Reachable inp u → ∀ c, ¬ Valent a u c → Valent a u (!c) := by
    intro u hu c hn
    obtain ⟨b, hb⟩ := hval u hu
    cases b <;> cases c <;> first | exact absurd hb hn | simpa using hb
  have hD₁ : Valent a (a.recvMsg m g₁) (!!b₀) := hother _ (hDreach g₁ hg₁C) _ h₁
  have hD₂ : ¬ Valent a (a.recvMsg m g₂) (!!b₀) := huni g₂ hg₂C _ h₂
  have hmg₁ := hmem g₁ hg₁C
  cases x with
  | none =>
      obtain rfl := Algorithm.tr_none htr
      exact h₁ h₂
  | some m' =>
      obtain ⟨hm', rfl⟩ := htr
      by_cases hd : m'.dest = m.dest
      · -- Case 2 of Fischer, Lynch and Paterson: both events at the process `p = m.dest`.
        obtain ⟨A, b, hA, hAd⟩ := hpt inp g₁ (hreach g₁ hg₁C) {m.dest}ᶜ
          (by simp [Set.ncard_compl {m.dest}])
        have hAr : a.Reachable inp A := Algorithm.reachable_stable (hreach g₁ hg₁C)
          (CanReachVia.canReach hA)
        have hp : DestIn ({m.dest} : Set P) (some m) := Set.mem_singleton _
        have hp' : DestIn ({m.dest} : Set P) (some m') := by
          simp [DestIn, hd]
        have e₀ : a.CanReachVia {m.dest} g₁ (a.recvMsg m g₁) :=
          CanReachVia.stepL hp ⟨hmg₁, rfl⟩ (CanReachVia.refl _ _)
        have e₁ : a.CanReachVia {m.dest} g₁ (a.recvMsg m (a.recvMsg m' g₁)) :=
          CanReachVia.stepL hp' ⟨hm', rfl⟩
            (CanReachVia.stepL hp ⟨hmem _ hg₂C, rfl⟩ (CanReachVia.refl _ _))
        obtain ⟨E₀, hE₀, hAE₀⟩ := CanReachVia.diamond e₀ hA
        obtain ⟨E₁, hE₁, hAE₁⟩ := CanReachVia.diamond e₁ hA
        -- `E₀` has only the value of `e(g₁)`, `E₁` only that of `e(g₂)`.
        have v₀ : Valent a E₀ (!!b₀) := by
          by_contra hn
          have := hother E₀ (Algorithm.reachable_stable (hDreach g₁ hg₁C)
            (CanReachVia.canReach hE₀)) _ hn
          exact h₁ (by simpa using valent_of_canReach (CanReachVia.canReach hE₀) this)
        have v₁ : Valent a E₁ (!b₀) := by
          by_contra hn
          have := hother E₁ (Algorithm.reachable_stable (hDreach _ hg₂C)
            (CanReachVia.canReach hE₁)) _ hn
          exact hD₂ (valent_of_canReach (CanReachVia.canReach hE₁) this)
        -- Then the decided state `A` reaches both values.
        have k₀ := hdec A b _ hAr hAd (valent_of_canReach (CanReachVia.canReach hAE₀) v₀)
        have k₁ := hdec A b _ hAr hAd (valent_of_canReach (CanReachVia.canReach hAE₁) v₁)
        cases b₀ <;> simp_all
      · -- Case 1: the events commute, so `e(g₂)` is reachable from `e(g₁)`.
        obtain ⟨hm'D, -, hcomm⟩ := Algorithm.recvMsg_comm (a := a) (Ne.symm hd) hmg₁ hm'
        have hreach₁₂ : a.lts.CanReach (a.recvMsg m g₁) (a.recvMsg m (a.recvMsg m' g₁)) := by
          rw [← hcomm]
          exact canReach_of_tr (x := some m') ⟨hm'D, rfl⟩
        exact h₁ (valent_of_canReach hreach₁₂ h₂)

end Bivalent

end Cslib.Distributed.FLP
