/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.GlobalProgress

/-!
# Both-side restriction extrusion and guarded continuation preservation
-/

namespace Cslib.SessionTypes.Endpoint.FrontierNormalizationTests

open PiCalculus

def leftBody : Proc := .out (.var 0) (.var 1) (.nu (.inp (.var 0) .nil))
def rightBody : Proc := .inp (.var 0) (.out (.var 0) (.const 7) .nil)
def source : Proc := .par (.nu leftBody) (.nu rightBody)

/-- Arbitrarily open ambient payload names are admitted by the GENERAL finite
normalizer. It is not a theorem restricted to closed partner holes. -/
theorem source_normalizes : ∃ q, Cong source q ∧ FrontierNormal q := by
  apply finiteLinear_frontier_normal
  simp [source, leftBody, rightBody, FiniteLinear]

/-- Both unguarded restrictions survive; the guarded restriction in leftBody
stays in its output continuation, and outer payload var1 is lifted to var2. -/
theorem exact_two_binder_shape :
    Cong source (.nu (.nu (.par (liftProc 0 leftBody) (liftProc 1 rightBody)))) := by
  exact Cong.trans (Cong.scope leftBody (.nu rightBody))
    (Cong.nu_cong (Cong.trans (Cong.par_comm leftBody (.nu (liftProc 1 rightBody)))
      (Cong.trans (Cong.scope (liftProc 1 rightBody) leftBody)
        (Cong.nu_cong (Cong.par_comm (liftProc 1 rightBody) (liftProc 0 leftBody))))))

/-- A frontier treats each actual prefix as a guard, not its continuation as
an already enabled future action. -/
theorem exact_two_binder_frontier :
    FrontierNormal (.nu (.nu (.par (liftProc 0 leftBody) (liftProc 1 rightBody)))) :=
  FrontierNormal.nu (FrontierNormal.nu (FrontierNormal.frontier
    (GuardFrontier.par (GuardFrontier.out _ _ _) (GuardFrontier.inp _ _))))

/-- All-nil restrictions are genuinely completed at process level. -/
theorem all_nil_restrictions_completed : Cong (.nu (.nu (.par .nil .nil))) .nil :=
  Cong.trans (Cong.nu_cong (Cong.nu_cong (Cong.par_nil .nil)))
    (Cong.trans (Cong.nu_cong Cong.nu_nil) Cong.nu_nil)

/-- The all-nil binder tower uses GENERAL global progress, with an explicit
ranked typing derived from its process-level completion and canonical Cong. -/
theorem all_nil_global_progress :
    Cong (.nu (.nu (.par .nil .nil))) .nil ∨
      ∃ q, PiCalculus.Step (.nu (.nu (.par .nil .nil))) q := by
  have hn : RankedType 0 ∅ .nil := RankedType.nil
    (by intro e c he; simp at he) (by intro e he; exact False.elim (Finmap.notMem_empty he))
  have ht := (RankedType.cong_iff all_nil_restrictions_completed).mpr hn
  exact ht.progress_empty

end Cslib.SessionTypes.Endpoint.FrontierNormalizationTests
