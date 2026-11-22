/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.PiCalculus.Scoping

/-!
# Light-import π scoping consumers

These tests import the Basic-only scoping interface without behavioural or
contextual theory. They exercise insertion/removal cutoffs, open payloads,
and nested input/restriction binders on the existing de Bruijn syntax.
-/

namespace Cslib.PiCalculus.ScopingTests

/-- Constants are free at any depth; a variable needs an actual binder. -/
theorem name_scope_boundaries (n : ℕ) :
    (Name.const 7).ClosedAt n ∧ ¬ (Name.var 0).ClosedAt 0 ∧
      (Name.var 0).ClosedAt 1 := by
  simp [Name.ClosedAt]

/-- Lifting at cutoff one leaves lower variables alone and shifts the
upper branch; both names remain scoped in the enlarged environment. -/
theorem name_lift_branches :
    liftName 1 (.var 0) = .var 0 ∧ liftName 1 (.var 1) = .var 2 ∧
      (liftName 1 (.var 0)).ClosedAt 3 ∧
      (liftName 1 (.var 1)).ClosedAt 3 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact Name.ClosedAt.lift (n := 2) (by simp [Name.ClosedAt])
  · exact Name.ClosedAt.lift (n := 2) (by simp [Name.ClosedAt])

/-- The cutoff side condition matters: skipping beyond the only ambient
binder would leave its variable dangling after the environment shrinks. -/
theorem name_subst_cutoff_counterexample :
    (Name.const 7).ClosedAt 0 ∧ (Name.var 0).ClosedAt 1 ∧
      ¬ (substName (.const 7) 1 (.var 0)).ClosedAt 0 := by
  simp [substName, Name.ClosedAt]

/-- Process lifting enters an input binder without shifting its newly
bound payload, while preserving the ambient channel reference. -/
theorem process_lift_input :
    liftProc 0 (.inp (.var 0) (.out (.var 1) (.var 0) .nil)) =
      .inp (.var 1) (.out (.var 2) (.var 0) .nil) ∧
    (liftProc 0 (.inp (.var 0) (.out (.var 1) (.var 0) .nil))).ClosedAt 2 := by
  refine ⟨rfl, Proc.ClosedAt.lift (n := 1) ?_⟩
  simp [Proc.ClosedAt, Name.ClosedAt]

/-- A free replacement crosses both restriction and input binders. The
input-bound object stays bound; the removed ambient subject becomes free. -/
theorem process_subst_two_binders :
    subst (.nu (.inp (.var 1) (.out (.var 2) (.var 0) .nil))) (.const 7) =
      .nu (.inp (.const 7) (.out (.const 7) (.var 0) .nil)) ∧
    (subst (.nu (.inp (.var 1) (.out (.var 2) (.var 0) .nil)))
      (.const 7)).ClosedAt 0 := by
  refine ⟨rfl, Proc.ClosedAt.subst ?_ trivial⟩
  simp [Proc.ClosedAt, Name.ClosedAt]

/-- An open replacement at the maximal admitted cutoff is lifted across
restriction instead of being captured by it. -/
theorem process_subst_outermost :
    substProc (.var 0) 1 (.nu (.out (.var 2) (.var 0) .nil)) =
      .nu (.out (.var 1) (.var 0) .nil) ∧
    (substProc (.var 0) 1 (.nu (.out (.var 2) (.var 0) .nil))).ClosedAt 1 := by
  refine ⟨rfl, Proc.ClosedAt.substProc ?_ ?_ (Nat.le_refl 1)⟩
  · simp [Proc.ClosedAt, Name.ClosedAt]
  · simp [Name.ClosedAt]

/-- Closed processes with two internal binders are fixed by external
lifting through the standalone scoping API. -/
theorem closed_lift_nested :
    liftProc 0 (.nu (.inp (.var 0) (.out (.var 1) (.var 0) .nil))) =
      .nu (.inp (.var 0) (.out (.var 1) (.var 0) .nil)) := by
  apply liftProc_eq_of_closedAt
  simp [Proc.ClosedAt, Name.ClosedAt]

/-- The source snapshot's cutoff-zero dot-notation call shape works
without a behavioural or contextual import. Source details are in
`docs/provenance/pi-scoping/manifest.json`. -/
theorem session_lift_call {n : ℕ} {b : Name} (h : b.ClosedAt n) :
    (liftName 0 b).ClosedAt (n + 1) := h.lift

end Cslib.PiCalculus.ScopingTests
