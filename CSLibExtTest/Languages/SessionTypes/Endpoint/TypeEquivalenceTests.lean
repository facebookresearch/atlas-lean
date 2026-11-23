/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.TypeEquivalence

/-!
# Distinct regular codes, finite bridges and branch/metadata rejection
-/

namespace Cslib.SessionTypes.Endpoint.TypeEquivalenceTests

def oneGraph : Graph := ⟨1, fun _ => .sendName ⟨0, by decide⟩⟩
def twoGraph : Graph := ⟨2, fun i => .sendName (if i.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩)⟩
def oneLoop : Protocol := .regular oneGraph ⟨0, by decide⟩ false
def twoLoop (i : Fin 2) : Protocol := .regular twoGraph i false

/-- One-state and two-state cyclic codes denote the same infinite send tree. -/
theorem different_cycles_equivalent (i : Fin 2) : oneLoop.TreeEquiv (twoLoop i) := by
  let R : Protocol → Protocol → Prop := fun p q => p = oneLoop ∧ ∃ j, q = twoLoop j
  apply Protocol.TreeEquiv.coind (R := R) ?_ ⟨rfl, i, rfl⟩
  intro p q hpq
  obtain ⟨rfl, j, rfl⟩ := hpq
  change HeadMatch R (.sendName oneLoop)
    (.sendName (twoLoop (if j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩)))
  exact HeadMatch.sendName ⟨rfl, _, rfl⟩

/-- This equivalence is not graph/cursor code equality. -/
theorem different_cycles_codes_unequal (i : Fin 2) : oneLoop ≠ twoLoop i := by
  intro h
  have hg : oneGraph = twoGraph := (Protocol.regular.inj h).1
  have hn := congrArg Graph.size hg
  change 1 = 2 at hn
  cases hn

def finiteGraph : Graph := ⟨2, fun i => if i.val = 0 then .sendName ⟨1, by decide⟩ else .done⟩
def finiteCode : Protocol := .regular finiteGraph ⟨0, by decide⟩ false
def finiteEnd : Protocol := .regular finiteGraph ⟨1, by decide⟩ false

/-- Graph-coded terminal state and finite completion denote the same tree. -/
theorem graph_end_equivalent : finiteEnd.TreeEquiv .done :=
  Protocol.treeEquiv_iff_head.mpr HeadMatch.done

/-- A finite constructor and a graph-coded finite protocol are equivalent. -/
theorem finite_graph_equivalent : finiteCode.TreeEquiv (.sendName .done) :=
  Protocol.treeEquiv_iff_head.mpr (HeadMatch.sendName graph_end_equivalent)

/-- Duality preserves the nontrivial code equivalence. -/
theorem different_cycles_duals_equivalent (i : Fin 2) :
    oneLoop.dual.TreeEquiv (twoLoop i).dual := (different_cycles_equivalent i).dual

/-- Wrong subject direction is semantically distinguishable even for cycles. -/
theorem wrong_cycle_direction : ¬ oneLoop.TreeEquiv (twoLoop ⟨0, by decide⟩).dual := by
  intro h
  have hh := h.head
  change HeadMatch Protocol.TreeEquiv (.sendName oneLoop)
    (.recvName (twoLoop ⟨1, by decide⟩).dual) at hh
  cases hh

/-- Payload role metadata is an observable part of the regular tree. -/
theorem wrong_payload_role : ¬
    (Protocol.sendEndpoint .positive 7 .done .done).TreeEquiv
      (.sendEndpoint .negative 7 .done .done) := by
  intro h
  have hh := h.head
  cases hh

/-- A different delegated rank is not equated by erasing annotations. -/
theorem wrong_payload_rank : ¬
    (Protocol.recvEndpoint .positive 7 .done .done).TreeEquiv
      (.recvEndpoint .positive 8 .done .done) := by
  intro h
  have hh := h.head
  cases hh

/-- Matching root direction is insufficient: a different continuation is rejected. -/
theorem different_continuation : ¬ (Protocol.sendName .done).TreeEquiv
    (.sendName (.recvName .done)) := by
  intro h
  have hh := h.head
  cases hh with
  | sendName ht =>
    have hh' := ht.head
    cases hh'

/-- Payload and continuation cannot be exchanged even when root metadata agrees. -/
theorem branches_not_interchangeable : ¬
    (Protocol.sendEndpoint .negative 11 (.sendName .done) .done).TreeEquiv
      (.sendEndpoint .negative 11 .done (.sendName .done)) := by
  intro h
  have hh := h.head
  cases hh with
  | sendEndpoint hp hs =>
    have hh' := hp.head
    cases hh'

/-- A genuinely recursive payload keeps its independent orientation under
subject duality, while the continuation becomes dual. -/
theorem payload_orientation_preserved :
    (Protocol.sendEndpoint .negative 11 oneLoop (twoLoop ⟨0, by decide⟩)).dual.TreeEquiv
      (.recvEndpoint .negative 11 (twoLoop ⟨1, by decide⟩) oneLoop.dual) := by
  exact (different_cycles_equivalent ⟨1, by decide⟩).recvEndpoint
    (different_cycles_equivalent ⟨0, by decide⟩).symm.dual .negative 11

/-- One root unfolding gives a different constructor code but the same tree. -/
theorem finite_code_not_constructor : finiteCode ≠ .sendName .done := by
  intro h
  cases h

/-- Repeated root unfolding does not change the infinite-cycle tree. -/
theorem recursive_unfold_equivalent : oneLoop.TreeEquiv (.sendName oneLoop) :=
  oneLoop.treeEquiv_unfold

/-- Equivalent terminal graph and finite constructor agree on completion. -/
theorem terminal_head_completion : finiteEnd.unfold = .done ↔ Protocol.done.unfold = .done :=
  graph_end_equivalent.done_iff

end Cslib.SessionTypes.Endpoint.TypeEquivalenceTests
