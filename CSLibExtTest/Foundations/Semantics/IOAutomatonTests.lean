/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.IOAutomaton

/-!
# Tests for input/output automata

A client and a server. The client outputs `req` and takes `resp` as input; the server takes
`req` as input, outputs `resp`, and has an internal action `tick`. They are strongly compatible,
and in their composition `req` and `resp` are outputs and nothing is an input.

* Pasting (Proposition 3): `[req, tick, resp]` is a schedule of the composition, because its
  projections `[req, resp]` and `[req, tick, resp]` are schedules of the client and the server.
* Its behaviour hides the internal `tick`: `[req, resp]` is a behaviour of the composition.
* Projection (Proposition 1): the server's projection of that behaviour is a behaviour of the
  server.
* Pasting behaviours (Proposition 3, behaviour form): `[req, resp]` is recovered as a behaviour
  of the composition from behaviours of the two components.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.IOAutomaton.Tests

/-- The actions of the example. -/
inductive Act
  | req
  | resp
  | tick
  deriving DecidableEq

open Act

/-- The client's signature: input `resp`, output `req`. -/
def clientSig : ActionSig Act where
  inp := {resp}
  out := {req}
  int := ∅
  disjoint_inp_out := by simp
  disjoint_inp_int := by simp
  disjoint_out_int := by simp

/-- The server's signature: input `req`, output `resp`, internal `tick`. -/
def serverSig : ActionSig Act where
  inp := {req}
  out := {resp}
  int := {tick}
  disjoint_inp_out := by simp
  disjoint_inp_int := by simp
  disjoint_out_int := by simp

/-- The client: its state records whether it is waiting for a response. -/
def client : IOAutomaton Act Bool where
  sig := clientSig
  start := {false}
  lts := ⟨fun s a t => (a = req ∧ s = false ∧ t = true) ∨ (a = resp ∧ t = false)⟩
  start_nonempty := Set.singleton_nonempty _
  mem_acts_of_tr := by
    rintro s a t (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp [clientSig, ActionSig.acts]
  input_enabled := by
    rintro s a ha
    simp only [clientSig, Set.mem_singleton_iff] at ha
    exact ⟨false, Or.inr ⟨ha, rfl⟩⟩

/-- The server: its state records whether a request is pending. -/
def server : IOAutomaton Act Bool where
  sig := serverSig
  start := {false}
  lts := ⟨fun s a t => (a = req ∧ t = true) ∨ (a = tick ∧ t = s) ∨
    (a = resp ∧ s = true ∧ t = false)⟩
  start_nonempty := Set.singleton_nonempty _
  mem_acts_of_tr := by
    rintro s a t (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp [serverSig, ActionSig.acts]
  input_enabled := by
    rintro s a ha
    simp only [serverSig, Set.mem_singleton_iff] at ha
    exact ⟨true, Or.inl ⟨ha, rfl⟩⟩

/-- The client and the server are strongly compatible. -/
theorem compatible : client.sig.StronglyCompatible server.sig where
  disjoint_out := by simp [client, server, clientSig, serverSig]
  disjoint_int_left := by simp [client, clientSig]
  disjoint_int_right := by simp [client, server, clientSig, serverSig, ActionSig.acts]

/-- In the composition nothing is an input: `req` and `resp` are both output by a component. -/
example (a : Act) : a ∉ (client.compose server compatible).sig.inp := by
  cases a <;> simp [IOAutomaton.compose, ActionSig.compose, client, server, clientSig, serverSig]

theorem client_sched : client.Sched (client.sig.proj [req, tick, resp]) := by
  rw [ActionSig.proj_cons_of_mem _ _ (by simp [client, clientSig, ActionSig.acts]),
    ActionSig.proj_cons_of_notMem _ _ (by simp [client, clientSig, ActionSig.acts]),
    ActionSig.proj_cons_of_mem _ _ (by simp [client, clientSig, ActionSig.acts]),
    ActionSig.proj_nil]
  exact ⟨false, rfl, false, .stepL (s2 := true) (Or.inl ⟨rfl, rfl, rfl⟩)
    (.stepL (s2 := false) (Or.inr ⟨rfl, rfl⟩) .refl)⟩

theorem server_sched : server.Sched (server.sig.proj [req, tick, resp]) := by
  rw [ActionSig.proj_cons_of_mem _ _ (by simp [server, serverSig, ActionSig.acts]),
    ActionSig.proj_cons_of_mem _ _ (by simp [server, serverSig, ActionSig.acts]),
    ActionSig.proj_cons_of_mem _ _ (by simp [server, serverSig, ActionSig.acts]),
    ActionSig.proj_nil]
  exact ⟨false, rfl, false, .stepL (s2 := true) (Or.inl ⟨rfl, rfl⟩)
    (.stepL (s2 := true) (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (.stepL (s2 := false) (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) .refl))⟩

/-- Pasting: `[req, tick, resp]` is a schedule of the composition. -/
theorem compose_sched : (client.compose server compatible).Sched [req, tick, resp] :=
  client.sched_of_proj server compatible
    (by
      intro a ha
      rw [IOAutomaton.compose, ActionSig.acts_compose]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;>
        simp [client, server, clientSig, serverSig, ActionSig.acts])
    client_sched server_sched

/-- The behaviour of that schedule hides the internal `tick`. -/
theorem compose_beh : (client.compose server compatible).Beh [req, resp] := by
  refine ⟨_, compose_sched, ?_⟩
  classical
  simp [ActionSig.extProj, ActionSig.ext, IOAutomaton.compose, ActionSig.compose, client,
    server, clientSig, serverSig]

/-- Projection: the server's part of that behaviour is a behaviour of the server. -/
example : server.Beh (server.sig.proj [req, resp]) :=
  client.beh_proj_right server compatible compose_beh

/-- Pasting behaviours: `[req, resp]` is a behaviour of the composition because its projections
are behaviours of the client and the server. -/
example : (client.compose server compatible).Beh [req, resp] := by
  refine client.beh_of_proj server compatible ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      simp [IOAutomaton.compose, ActionSig.compose, ActionSig.ext, client, server, clientSig,
        serverSig]
  · exact client.beh_proj_left server compatible compose_beh
  · exact client.beh_proj_right server compatible compose_beh

end Cslib.IOAutomaton.Tests
