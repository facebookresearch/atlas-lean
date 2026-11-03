/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SharedServices
public import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Quiescent services are not finite nil completion

The existing input-presence invariant rejects absent-service requests.
Its complementary output-presence observation rejects idle service reductions,
even after arbitrary canonical Cong and repl_unfold. Neither is ready-pair data.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Output presence outside every communication prefix, as actual Pi syntax. -/
def HasUnguardedOutput : Proc → Prop
  | .nil | .inp .. => False
  | .out .. => True
  | .par p q | .sum p q => HasUnguardedOutput p ∨ HasUnguardedOutput q
  | .nu p | .repl p => HasUnguardedOutput p

private theorem output_lift (k : Nat) (p : Proc) :
    HasUnguardedOutput (liftProc k p) ↔ HasUnguardedOutput p := by
  induction p generalizing k <;> simp_all [HasUnguardedOutput, liftProc]

private theorem output_swap (k : Nat) (p : Proc) :
    HasUnguardedOutput (swapProc k p) ↔ HasUnguardedOutput p := by
  induction p generalizing k <;> simp_all [HasUnguardedOutput, swapProc]

/-- Every one of the16 canonical Cong rules preserves actual exposed output presence. -/
theorem output_cong {p q : Proc} (h : Cong p q) :
    HasUnguardedOutput p ↔ HasUnguardedOutput q := by
  induction h <;> simp_all [HasUnguardedOutput, output_lift, output_swap, or_assoc, or_comm]

/-- A selected exposed output must have been present in the actual source syntax. -/
theorem output_select {p q : Proc} (h : Select p q) (hq : HasUnguardedOutput q) :
    HasUnguardedOutput p := by
  induction h with
  | refl => exact hq
  | left => exact Or.inl hq
  | right => exact Or.inr hq
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hq)

/-- Every actual canonical Step needs an output, including Cong/selection/replication. -/
theorem Step.source_hasUnguardedOutput {p q : Proc} (h : Step p q) :
    HasUnguardedOutput p := by
  induction h with
  | commSelect hs _ => exact Or.inl (output_select hs trivial)
  | parL _ ih => exact Or.inl ih
  | parR _ ih => exact Or.inr ih
  | nu _ ih => exact ih
  | cong hc _ _ ih => exact (output_cong hc).mpr ih

namespace Runtime

/-- Idle is syntax-only and excludes an exposed output even inside parallel/restriction. -/
theorem Idle.no_unguarded_output {Γ : ServiceEnv} {p : Proc} (h : Idle Γ p) :
    ¬ HasUnguardedOutput p := by
  induction p with
  | nil => simp [HasUnguardedOutput]
  | out => exact False.elim h
  | inp => simp [HasUnguardedOutput]
  | par p q ihp ihq =>
    intro ho
    cases ho with
    | inl ho => exact ihp h.1 ho
    | inr ho => exact ihq h.2 ho
  | nu p ih => exact ih h
  | repl p ih => exact ih h
  | sum => exact False.elim h

/-- Idle services cannot Step, even through arbitrary canonical structural congruence. -/
theorem Idle.no_step {Γ : ServiceEnv} {p : Proc} (h : Idle Γ p) (q : Proc) :
    ¬ PiCalculus.Step p q := fun hs =>
  h.no_unguarded_output (Endpoint.Step.source_hasUnguardedOutput hs)

end Runtime

end Cslib.SessionTypes.Endpoint
