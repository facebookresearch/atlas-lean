/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.CslibBridge
public import CSLibExt.Foundations.Semantics.LTS.WeakCslibBridge

@[expose] public section

set_option autoImplicit false

namespace Cslib.Semantics.LTS.WeakBridgeTests

open Cslib.LTS

/-- Silent label `0`, visible label `1`, over natural-number labels. -/
instance : _root_.Cslib.HasTau ℕ := ⟨0⟩

/-- Toy chain: `0` silently steps to `1`, then visibly to `2`. -/
def toy : _root_.Cslib.LTS ℕ ℕ :=
  ⟨fun a μ b => (a = 0 ∧ μ = 0 ∧ b = 1) ∨ (a = 1 ∧ μ = 1 ∧ b = 2)⟩

private theorem step01 : toy.Tr 0 0 1 := Or.inl ⟨rfl, rfl, rfl⟩

private theorem step12 : toy.Tr 1 1 2 := Or.inr ⟨rfl, rfl, rfl⟩

private theorem toyWeak : toy.STr 0 1 2 := by
  exact _root_.Cslib.LTS.STr.tr
    (τSTr.cons step01 τSTr.refl) step12 τSTr.refl

/-- A weak step on the toy chain is a saturated step. -/
example : (toCslib toy).STr 0 1 2 :=
  toyWeak

/-- Rooted tau steps are not reflexive at a state with no transitions. -/
example : ¬ RootedSTr (toCslib toy) 2 0 2 := by
  intro hroot
  have h : Relation.TransGen (fun a b => toy.Tr a 0 b) 2 2 :=
    (rootedSTr_tau_iff_transGen (lts := toy)).mp hroot
  cases h with
  | single hstep =>
      rcases hstep with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega
  | tail _ hstep =>
      rcases hstep with ⟨-, -, h⟩ | ⟨-, h, -⟩ <;> omega

/-- At a visible label, rooted and plain weak steps coincide. -/
example : RootedWeakStep (lts := toy) 0 1 2 :=
  ⟨1, 2, τSTr.cons step01 τSTr.refl, step12, τSTr.refl⟩

/-- The SMTr filter drops the silent label from the toy weak trace. -/
example : (toCslib toy).SMTr 0 [1] 2 := by
  have htrace : (toCslib toy).saturate.MTr 0 [1] 2 :=
    _root_.Cslib.LTS.MTr.stepL toyWeak _root_.Cslib.LTS.MTr.refl
  have h := saturate_mTr_to_sMTr htrace
  simpa using h

/-- Silent closure across the toy chain is a tau multistep upstream. -/
example : (toCslib toy).τSTr 0 1 :=
  τSTr.cons (.inl ⟨rfl, rfl, rfl⟩) τSTr.refl

end Cslib.Semantics.LTS.WeakBridgeTests
