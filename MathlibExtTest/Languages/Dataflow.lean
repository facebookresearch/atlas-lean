/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.Dataflow

@[expose] public section

/-- Boundary check: Kildall iteration on `Bool` stabilizes for a
monotone transfer function. -/
example : ∃ k, (fun b : Bool => b || true)^[k] (⊥ : Bool)
    = (fun b : Bool => b || true) ((fun b : Bool => b || true)^[k] (⊥ : Bool)) :=
  kildall_stabilizes (fun b : Bool => b || true) (fun a b h => by
    cases a <;> cases b <;> simp_all)
