/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Translation.TM2ToTM0

@[expose] public section

/-!
# Tests for the multi-stack to single-tape translation
-/

set_option autoImplicit false

open Turing MetaMathlibExt.TM2ToTM0

namespace MathlibExtTest.Computability.TuringMachine.Translation

/-- A one-stack machine that halts at once. -/
def haltM : Unit → TM2.Stmt (fun _ : Unit ↦ Bool) Unit Unit := fun _ ↦ .halt

/-- It halts on every input. -/
theorem haltM_eval_dom (L : List Bool) : (TM2.eval haltM () L).Dom := by
  rw [TM2.eval, Part.map_Dom]
  exact Part.dom_iff_mem.mpr ⟨_, StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.single rfl, rfl⟩⟩

/-- So its single-tape emulation halts on the encoded input. -/
example (L : List Bool) : (TM0.eval (tr haltM) (TM2to1.trInit () L)).Dom :=
  (tr_eval_dom haltM () L).mpr (haltM_eval_dom L)

/-- The emulation has a finite support. -/
example : TM0.Supports (tr haltM)
    ↑(TM1to0.trStmts (TM2to1.tr haltM) (TM2to1.trSupp haltM Finset.univ)) :=
  tr_supports haltM (supports_univ haltM)

end MathlibExtTest.Computability.TuringMachine.Translation
