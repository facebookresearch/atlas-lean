/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.CellProbe

/-!
# Cell-probe execution tests
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CellProbe

private def initial (tag : BitVec 4) : Memory 3 4 := fun i =>
  if i = 0 then tag else if i = 1 then 7 else 11

-- The pure calculation leaves all cells unchanged and makes no probes.
example : (Program.pure ((5 + 7) * 2 : Nat)).run (initial 1) = ⟨24, initial 1, 0⟩ := rfl

-- Returning is possible even when there is no address to probe.
example (memory : Memory 0 4) : (Program.pure true).run memory = ⟨true, memory, 0⟩ := rfl

-- Zero-bit cells still admit reads and writes, and each occurrence counts.
example :
    let program : Program 1 0 (BitVec 0) := .write 0 0 (.read 0 fun word => .pure word)
    let run := program.run (fun _ => 0)
    run.result = 0 ∧ run.memory 0 = 0 ∧ run.probes = 2 := by
  decide +kernel

private def adaptive : Program 3 4 (BitVec 4 × BitVec 4) :=
  .read 0 fun tag =>
    if tag = 0 then .pure (tag, tag)
    else
      let address : Fin 3 := if tag = 1 then 1 else 2
      .write address (tag + 4) <|
        .read address fun first =>
          .write address first <|
            .read address fun second =>
              .pure (first, second)

-- The short branch costs only its initial read.
example : adaptive.run (initial 0) = ⟨(0, 0), initial 0, 1⟩ := rfl

-- Both reads see the new word. The repeated read and same-value write still count.
example :
    let run := adaptive.run (initial 1)
    run.result = (5, 5) ∧ run.probes = 5 ∧
      run.memory 0 = 1 ∧ run.memory 1 = 5 ∧ run.memory 2 = 11 := by
  decide +kernel

-- Changing only the first word can redirect the later probes to a different cell.
example :
    let run := adaptive.run (initial 2)
    run.result = (6, 6) ∧ run.probes = 5 ∧
      run.memory 0 = 2 ∧ run.memory 1 = 7 ∧ run.memory 2 = 6 := by
  decide +kernel

end Cslib.Algorithms.Lean.CellProbe
