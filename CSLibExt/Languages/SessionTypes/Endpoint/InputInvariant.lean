/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Fragment

/-!
# Necessary input-guard presence for an existing π step

This syntactic invariant is a rejection tool, not an enabled-edge or
CanReduce witness and not a second execution semantics.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Unguarded input in a process.** An input is exposed outside every communication guard. -/
def HasUnguardedInput : Proc → Prop
  | .nil | .out .. => False
  | .inp .. => True
  | .par p q | .sum p q => HasUnguardedInput p ∨ HasUnguardedInput q
  | .nu p | .repl p => HasUnguardedInput p

private theorem input_lift (k : Nat) (p : Proc) :
    HasUnguardedInput (liftProc k p) ↔ HasUnguardedInput p := by
  induction p generalizing k <;> simp_all [HasUnguardedInput, liftProc]

private theorem input_swap (k : Nat) (p : Proc) :
    HasUnguardedInput (swapProc k p) ↔ HasUnguardedInput p := by
  induction p generalizing k <;> simp_all [HasUnguardedInput, swapProc]

/-- **Structural congruence preserves unguarded inputs.**
Every existing structural congruence preserves exposed input presence. -/
theorem input_cong {p q : Proc} (h : Cong p q) :
    HasUnguardedInput p ↔ HasUnguardedInput q := by
  induction h <;> simp_all [HasUnguardedInput, input_lift, input_swap,
    or_assoc, or_comm]

/-- **Selection reflects unguarded inputs.**
Selection cannot hide an input that is present in its selected term. -/
theorem input_select {p q : Proc} (h : Select p q) (hq : HasUnguardedInput q) :
    HasUnguardedInput p := by
  induction h with
  | refl => exact hq
  | left => exact Or.inl hq
  | right => exact Or.inr hq
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hq)

/-- **Every π step source has an unguarded input.**
Every existing π step requires an exposed input in its source,
including pre-congruence, selection, context closure and replication folding. -/
theorem Step.source_hasUnguardedInput {p q : Proc} (h : Step p q) :
    HasUnguardedInput p := by
  induction h with
  | commSelect _ ht => exact Or.inr (input_select ht trivial)
  | parL _ ih => exact Or.inl ih
  | parR _ ih => exact Or.inr ih
  | nu _ ih => exact ih
  | cong hc _ _ ih => exact (input_cong hc).mpr ih

end Cslib.SessionTypes.Endpoint
