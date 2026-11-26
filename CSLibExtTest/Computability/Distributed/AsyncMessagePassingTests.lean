/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.AsyncMessagePassing
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# Tests for asynchronous message-passing systems

The client-server example of Aspnes's notes (Section 2.2.1): process `0`, the client, sends a
request to process `1`, the server, which answers every request it receives with a response.

* An explicit execution of three events, a computation event of the client and two delivery
  events, ends with the client holding the response.
* Admissible executions exist, and in every admissible execution the client eventually receives
  the response: the reliable-delivery condition is not vacuous.
* With lossy channels the request may never be delivered: an execution admissible with lossy
  channels in which the client never receives the response, which is therefore not admissible.
* With no processes there is no infinite execution at all, so the extension theorem needs a
  process.
-/

@[expose] public section

namespace Cslib.Distributed.AsyncMessagePassing.Tests

open Filter Protocol

/-- The messages of the client-server example. -/
inductive Msg
  | request
  | response
  deriving DecidableEq

/-- The network of the example: an edge each way between the two processes. -/
def net : Digraph (Fin 2) := ⟨fun i j => i ≠ j⟩

/-- The client-server protocol. The client, in state `0` at first, sends the request in its first
event and moves to state `1`; once the response is delivered to it, it moves to state `2`. The
server sends one response for each request delivered to it. -/
def clientServer : Protocol net ℕ Msg where
  init _ := {0}
  trans i q A :=
    if i = 0 then
      if q = 0 then (1, {(1, .request)})
      else if (1, .response) ∈ A then (2, 0) else (q, 0)
    else (q, (A.filter (· = (0, .request))).map fun _ => (0, .response))
  adj_of_mem_trans i q A x hx := by
    change i ≠ x.1
    by_cases hi : i = 0
    · subst hi
      simp only [↓reduceIte] at hx
      split_ifs at hx
      · rw [Multiset.mem_singleton.mp hx]
        decide
      · simp at hx
      · simp at hx
    · simp only [hi, ↓reduceIte] at hx
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp hx
      exact hi

/-- The initial configuration. -/
def C₀ : Config (Fin 2) ℕ Msg := ⟨fun _ => 0, fun _ _ => 0⟩

theorem isInitial_C₀ : clientServer.IsInitial C₀ :=
  ⟨fun _ => Set.mem_singleton_iff.mpr rfl, fun _ _ => rfl⟩

/-- A computation event of the client: it sends the request. -/
def e₁ : Event (Fin 2) Msg := ⟨0, 0⟩

/-- The server receives the request and sends the response. -/
def e₂ : Event (Fin 2) Msg := ⟨1, {(0, .request)}⟩

/-- The client receives the response. -/
def e₃ : Event (Fin 2) Msg := ⟨0, {(1, .response)}⟩

/-- The configuration after `e₁`. -/
noncomputable def C₁ : Config (Fin 2) ℕ Msg := clientServer.applyEvent C₀ e₁

/-- The configuration after `e₂`. -/
noncomputable def C₂ : Config (Fin 2) ℕ Msg := clientServer.applyEvent C₁ e₂

/-- The configuration after `e₃`. -/
noncomputable def C₃ : Config (Fin 2) ℕ Msg := clientServer.applyEvent C₂ e₃

/-- The three events form an execution. -/
theorem isExecution_three :
    clientServer.IsExecution C₀ [e₁, e₂, e₃] C₃ [C₀, C₁, C₂, C₃] :=
  ⟨isInitial_C₀, .stepL ⟨by decide, rfl⟩ <| .stepL ⟨by decide, rfl⟩ <|
    .stepL ⟨by decide, rfl⟩ <| .refl _⟩

-- After `e₁` the request is in transit to the server, after `e₂` the response to the client.
example : C₁.chan 0 1 = {.request} ∧ C₁.state 0 = 1 := by decide
example : C₂.chan 0 1 = 0 ∧ C₂.chan 1 0 = {.response} := by decide
-- At the end the client holds the response and every channel is empty.
example : C₃.state 0 = 2 ∧ ∀ i j, C₃.chan i j = 0 := by decide

-- An event that delivers a message not in transit is not a transition.
example : ¬ clientServer.lts.Tr C₀ e₂ (clientServer.applyEvent C₀ e₂) := by
  rintro ⟨h, -⟩
  exact absurd (h 0) (by decide)

-- A process has no channel to itself, so it never holds a message.
example : C₃.chan 0 0 = 0 := isExecution_three.chan_eq_zero_of_not_adj (by simp [net])

/-- The client-server protocol has an admissible execution, indeed one that starts with the
three events above. -/
theorem exists_isAdmissible :
    ∃ Cs φs, clientServer.IsAdmissible ([C₀, C₁, C₂, C₃] ++ω Cs) ([e₁, e₂, e₃] ++ω φs) :=
  isExecution_three.exists_isAdmissible_extension

section Eventually

variable {Cs : ωSequence (Config (Fin 2) ℕ Msg)} {φs : ωSequence (Event (Fin 2) Msg)}

theorem state_succ (h : clientServer.lts.OmegaExecution Cs φs) (n : ℕ) :
    (Cs (n + 1)).state 0 =
      if 0 = (φs n).proc then
        (clientServer.trans (φs n).proc ((Cs n).state (φs n).proc) (φs n).delivered).1
      else (Cs n).state 0 := by
  rw [(h n).2]
  simp only [applyEvent, Function.update_apply]

theorem chan_succ (h : clientServer.lts.OmegaExecution Cs φs) (n : ℕ) (i j : Fin 2) :
    (Cs (n + 1)).chan i j =
      (Cs n).chan i j -
          (if j = (φs n).proc then ((φs n).delivered.filter (·.1 = i)).map Prod.snd else 0) +
        if i = (φs n).proc then
          ((clientServer.trans (φs n).proc ((Cs n).state (φs n).proc)
            (φs n).delivered).2.filter (·.1 = j)).map Prod.snd
        else 0 := by
  rw [(h n).2]
  rfl

/-- Once the client has left state `0`, it never returns to it. -/
theorem state_ne_zero_succ (h : clientServer.lts.OmegaExecution Cs φs) {n : ℕ}
    (hn : (Cs n).state 0 ≠ 0) : (Cs (n + 1)).state 0 ≠ 0 := by
  rw [state_succ h]
  split_ifs with hp
  · rw [← hp]
    simp only [clientServer, ite_true, ite_eq_right hn]
    split_ifs <;> simp [hn]
  · exact hn

theorem state_ne_zero_add (h : clientServer.lts.OmegaExecution Cs φs) {n : ℕ}
    (hn : (Cs n).state 0 ≠ 0) (d : ℕ) : (Cs (n + d)).state 0 ≠ 0 := by
  induction d with
  | zero => exact hn
  | succ d ih => exact state_ne_zero_succ h ih

/-- In every admissible execution of the client-server protocol, the client eventually receives
the response. -/
theorem client_done (h : clientServer.IsAdmissible Cs φs) : ∃ n, (Cs n).state 0 = 2 := by
  obtain ⟨⟨⟨hinit, hex⟩, hcomp⟩, hdel⟩ := h
  have h0 : (Cs 0).state 0 = 0 := hinit.1 0
  -- The client takes an event, after which it is no longer in state `0`.
  have hleave : ∃ n, (Cs n).state 0 ≠ 0 := by
    obtain ⟨k, -, hk, -⟩ := frequently_atTop.mp (hcomp 0) 0
    refine ⟨k + 1, ?_⟩
    rw [state_succ hex, ite_eq_left hk.symm, hk]
    simp only [clientServer, ite_true]
    split_ifs <;> simp_all
  classical
  -- At the first step at which the client leaves state `0`, it sends the request.
  have hk0 : Nat.find hleave ≠ 0 := fun h' => Nat.find_spec hleave (by rw [h']; exact h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hbefore : (Cs k).state 0 = 0 := by
    by_contra hne
    exact Nat.find_min hleave (by omega : k < Nat.find hleave) hne
  have hafter : (Cs (k + 1)).state 0 ≠ 0 := by
    have := Nat.find_spec hleave
    rwa [hk] at this
  have hproc : (φs k).proc = 0 := by
    by_contra hp
    rw [state_succ hex, ite_eq_right (Ne.symm hp)] at hafter
    exact hafter hbefore
  have hreq : Msg.request ∈ (Cs (k + 1)).chan 0 1 := by
    rw [chan_succ hex, hproc]
    simp [clientServer, hbefore]
  -- The server receives the request and sends the response.
  obtain ⟨k₁, hk₁, hp₁, hd₁⟩ := hdel (k + 1) 0 1 _ hreq
  have hresp : Msg.response ∈ (Cs (k₁ + 1)).chan 1 0 := by
    rw [chan_succ hex, hp₁]
    simp only [clientServer, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true]
    refine Multiset.mem_of_le (Multiset.le_add_left _ _) ?_
    rw [Multiset.mem_map]
    refine ⟨(0, .response), ?_, rfl⟩
    rw [Multiset.mem_filter]
    refine ⟨Multiset.mem_map.mpr ⟨(0, .request), Multiset.mem_filter.mpr ⟨hd₁, rfl⟩, rfl⟩, rfl⟩
  -- The client receives the response, in a state other than `0`.
  obtain ⟨k₂, hk₂, hp₂, hd₂⟩ := hdel (k₁ + 1) 1 0 _ hresp
  have hq : (Cs k₂).state 0 ≠ 0 := by
    have := state_ne_zero_add hex hafter (k₂ - (k + 1))
    rwa [show k + 1 + (k₂ - (k + 1)) = k₂ by omega] at this
  refine ⟨k₂ + 1, ?_⟩
  rw [state_succ hex, ite_eq_left hp₂.symm, hp₂]
  simp [clientServer, hq, hd₂]

end Eventually

/-- The configuration in which the request is in transit for ever. -/
noncomputable def lossyConfigs : ωSequence (Config (Fin 2) ℕ Msg) := ⟨fun n => if n = 0 then C₀ else C₁⟩

/-- The client sends the request, then the two processes alternate computation events. -/
def lossyEvents : ωSequence (Event (Fin 2) Msg) := ⟨fun n => ⟨if n % 2 = 0 then 0 else 1, 0⟩⟩

theorem applyEvent_C₁_computation (i : Fin 2) : clientServer.applyEvent C₁ ⟨i, 0⟩ = C₁ := by
  have hs : ∀ i j : Fin 2, (clientServer.applyEvent C₁ ⟨i, 0⟩).state j = C₁.state j := by decide
  have hc : ∀ i j k : Fin 2, (clientServer.applyEvent C₁ ⟨i, 0⟩).chan j k = C₁.chan j k := by
    decide
  exact Config.ext (funext (hs i)) (funext fun j => funext (hc i j))

/-- An execution admissible with lossy channels in which the request is never delivered. -/
theorem isLossyAdmissible_lossy : clientServer.IsLossyAdmissible lossyConfigs lossyEvents := by
  refine ⟨⟨isInitial_C₀, fun n => ?_⟩, fun i => frequently_atTop.mpr fun N => ?_⟩
  · rcases n with _ | n
    · exact ⟨by decide, rfl⟩
    · refine ⟨fun _ => ?_, ?_⟩
      · exact (Multiset.zero_le _ : (0 : Multiset Msg) ≤ _)
      · exact (applyEvent_C₁_computation _).symm
  · fin_cases i
    · exact ⟨2 * N, by omega, by simp [lossyEvents]⟩
    · exact ⟨2 * N + 1, by omega, by simp [lossyEvents, Nat.add_mod]⟩

-- No configuration of an infinite execution has a message on a channel off the network.
example (n : ℕ) : (lossyConfigs n).chan 1 1 = 0 :=
  isLossyAdmissible_lossy.1.chan_eq_zero_of_not_adj n (by simp [net])

theorem lossy_never_done (n : ℕ) : (lossyConfigs n).state 0 ≠ 2 := by
  change (if n = 0 then C₀ else C₁).state 0 ≠ 2
  split_ifs <;> decide

/-- With lossy channels the client may never receive the response, so this execution is not
admissible. -/
theorem not_isAdmissible_lossy : ¬ clientServer.IsAdmissible lossyConfigs lossyEvents := by
  intro h
  obtain ⟨n, hn⟩ := client_done h
  exact lossy_never_done n hn

/-- With no processes there is no event, hence no infinite execution. -/
example {Q M : Type*} {G : Digraph Empty} (π : Protocol G Q M) [DecidableEq M]
    (Cs : ωSequence (Config Empty Q M)) (φs : ωSequence (Event Empty M)) :
    ¬ π.IsInfiniteExecution Cs φs :=
  fun _ => (φs 0).proc.elim

end Cslib.Distributed.AsyncMessagePassing.Tests
