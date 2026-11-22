/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.REComplete

@[expose] public section

/-!
# Tests for the r.e.-completeness of the halting set
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.REComplete

/-- The code `comp succ (const 4)` returns `5` on every input. -/
example : (Code.comp Code.succ (Code.const 4)).eval 7 = Part.some 5 := by
  rw [eval_comp_const]
  rfl

/-- A decidable set reduces to the halting set. -/
example : ManyOneReducible (fun n : ℕ ↦ n = 3) haltingSet := by
  classical
  refine manyOneReducible_haltingSet (ComputablePred.to_re ?_)
  exact ComputablePred.computable_iff.mpr ⟨fun n ↦ decide (n = 3),
    (Primrec.eq.decide.comp Primrec.id (Primrec.const 3)).to_comp, by funext n; simp⟩

/-- The halting set is r.e.-complete. -/
example : REPred haltingSet ∧ ∀ p : ℕ → Prop, REPred p → ManyOneReducible p haltingSet :=
  ⟨rePred_haltingSet, fun _ ↦ manyOneReducible_haltingSet⟩

/-- Its complement is not recognizable, hence not many-one reducible to it. -/
example : ¬ManyOneReducible (fun n ↦ ¬haltingSet n) haltingSet := fun h ↦
  not_computablePred_haltingSet (ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨rePred_haltingSet, REPred.of_manyOneReducible h rePred_haltingSet⟩)

/-- The halting set is even one-one complete. -/
example {p : ℕ → Prop} : REPred p ↔ OneOneReducible p haltingSet :=
  rePred_iff_oneOneReducible_haltingSet

example {p : ℕ → Prop} : TM2Recognizable p ↔ ManyOneReducible p haltingSet :=
  tm2Recognizable_iff_manyOneReducible_haltingSet

end CSLibExtTest.Computability.Decidability.REComplete
