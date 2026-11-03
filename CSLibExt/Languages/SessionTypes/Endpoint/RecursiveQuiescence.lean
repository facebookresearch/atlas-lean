/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SharedServices
public import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant
public import CSLibExt.Languages.PiCalculus.Behavioural

/-!
# Quiescent services are not finite nil completion

Canonical Pi output presence and its Step invariant exclude idle reductions.
The endpoint input invariant separately rejects absent-service requests.
Neither observation stores readiness or a reduction witness.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Idle is syntax-only and excludes a canonical exposed output, including
inside parallel, restriction and inert replicated templates. -/
theorem Idle.no_unguarded_output {Γ : ServiceEnv} {p : Proc} (h : Idle Γ p) :
    ¬ PiCalculus.HasUnguardedOutput p := by
  induction p with
  | nil => simp [PiCalculus.HasUnguardedOutput]
  | out => exact False.elim h
  | inp => simp [PiCalculus.HasUnguardedOutput]
  | par p q ihp ihq =>
    intro ho
    cases ho with
    | inl ho => exact ihp h.1 ho
    | inr ho => exact ihq h.2 ho
  | nu p ih => exact ih h
  | repl p ih => exact ih h
  | sum => exact False.elim h

/-- Idle services cannot Step, even through arbitrary canonical congruence. -/
theorem Idle.no_step {Γ : ServiceEnv} {p : Proc} (h : Idle Γ p) (q : Proc) :
    ¬ PiCalculus.Step p q := fun hs => h.no_unguarded_output hs.hasUnguardedOutput

end Cslib.SessionTypes.Endpoint.Runtime
