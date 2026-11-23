/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Graph

/-!
# Name and capability protocols with guarded regular recursion

Finite constructors distinguish passive names from linear endpoint payloads.
A regular graph cursor adds recursion without changing the finite API.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- A protocol with explicit payload sort and guarded graph recursion.
Payload endpoint roles are transmitted unchanged, not dualized. -/
inductive Protocol where
  | done
  | sendName (next : Protocol)
  | recvName (next : Protocol)
  | sendEndpoint (role : Role) (rank : Nat) (payload next : Protocol)
  | recvEndpoint (role : Role) (rank : Nat) (payload next : Protocol)
  | regular (graph : Graph) (cursor : Fin graph.size) (reversed : Bool)

/-- Reverse subject actions and continuations; preserve payload ownership. -/
def Protocol.dual : Protocol → Protocol
  | .done => .done
  | .sendName s => .recvName s.dual
  | .recvName s => .sendName s.dual
  | .sendEndpoint r k t s => .recvEndpoint r k t s.dual
  | .recvEndpoint r k t s => .sendEndpoint r k t s.dual
  | .regular g i b => .regular g i (!b)

/-- Duality is involutive for finite and guarded recursive protocols. -/
@[simp] theorem Protocol.dual_dual (s : Protocol) : s.dual.dual = s := by
  induction s <;> simp [dual, *]

/-- Expose one communication guard. Graph successors retain their subject
orientation; an endpoint payload retains its independently specified one. -/
def Protocol.unfold : Protocol → Protocol
  | .regular g i b =>
    match g.node i with
    | .done => .done
    | .sendName j =>
      if b then .recvName (.regular g j b)
      else .sendName (.regular g j b)
    | .recvName j =>
      if b then .sendName (.regular g j b)
      else .recvName (.regular g j b)
    | .sendEndpoint r k t tb j =>
      if b then .recvEndpoint r k (.regular g t tb) (.regular g j b)
      else .sendEndpoint r k (.regular g t tb) (.regular g j b)
    | .recvEndpoint r k t tb j =>
      if b then .sendEndpoint r k (.regular g t tb) (.regular g j b)
      else .recvEndpoint r k (.regular g t tb) (.regular g j b)
  | s => s

/-- Guarded unfolding commutes with duality, including recursive payloads. -/
theorem Protocol.unfold_dual (s : Protocol) :
    s.dual.unfold = s.unfold.dual := by
  cases s <;> try rfl
  rename_i g i b
  cases h : g.node i <;> cases b <;> simp [dual, unfold, h]

/-- Unfolding always exposes an action or completion, never another silent
regular-cursor wrapper. Cycles therefore cannot consist only of unfolding. -/
theorem Protocol.unfold_ne_regular (s : Protocol) (g : Graph)
    (i : Fin g.size) (b : Bool) : s.unfold ≠ .regular g i b := by
  cases s with
  | regular h j c =>
    cases hn : h.node j <;> cases c <;> simp [unfold, hn]
  | _ => simp [unfold]

/-- One root unfolding is enough to expose a guard or completion. -/
@[simp] theorem Protocol.unfold_unfold (s : Protocol) :
    s.unfold.unfold = s.unfold := by
  cases s with
  | regular g i b =>
    cases h : g.node i <;> cases b <;> simp [unfold, h]
  | _ => rfl

end Cslib.SessionTypes.Endpoint
