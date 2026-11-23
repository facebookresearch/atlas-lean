/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Depth

/-!
# Appending a gate as a new circuit output

`Circuit.snocLine c line` appends `line` to the program of `c` as its last gate and designates
that gate as a new last output, after the outputs of `c`. Building a circuit gate by gate this way
keeps every gate built so far available as an output. The lemmas below give the program, the
size, the outputs, and the values and depths of the old outputs and of the new one, for every
signature.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {n k : ℕ}

/-- Append `line` to the program of `c` as its last gate, and add that gate as a new last output
after the outputs of `c`. -/
def Circuit.snocLine (c : Circuit σ n k) (line : Line σ n c.size) : Circuit σ n (k + 1) :=
  ⟨c.program.gate line, Fin.snoc (fun t => (c.outputs t).castSucc) (.gate (Fin.last c.size))⟩

/-- The program of `c.snocLine line` is the program of `c` followed by `line`. -/
@[simp] theorem Circuit.program_snocLine (c : Circuit σ n k) (line : Line σ n c.size) :
    (c.snocLine line).program = c.program.gate line := rfl

/-- `snocLine` adds one gate. -/
@[simp] theorem Circuit.size_snocLine (c : Circuit σ n k) (line : Line σ n c.size) :
    (c.snocLine line).size = c.size + 1 := rfl

/-- The earlier outputs keep their wires. -/
@[simp] theorem Circuit.outputs_snocLine_castSucc (c : Circuit σ n k) (line : Line σ n c.size)
    (t : Fin k) : (c.snocLine line).outputs t.castSucc = (c.outputs t).castSucc := by
  simp [snocLine]

/-- The new last output is the new gate. -/
@[simp] theorem Circuit.outputs_snocLine_last (c : Circuit σ n k) (line : Line σ n c.size) :
    (c.snocLine line).outputs (Fin.last k) = .gate (Fin.last c.size) := by
  simp [snocLine]

/-- The earlier outputs keep their values. -/
@[simp] theorem Circuit.eval_snocLine_castSucc (c : Circuit σ n k) (line : Line σ n c.size)
    (I : Interpretation σ U) (x : Fin n → U) (t : Fin k) :
    (c.snocLine line).eval I x t.castSucc = c.eval I x t := by
  change (c.program.gate line).trace I x ((c.snocLine line).outputs t.castSucc) =
    c.program.trace I x (c.outputs t)
  rw [outputs_snocLine_castSucc, Program.trace_gate_castSucc]

/-- The new last output is the value of `line` on the inputs and the gates of `c`. -/
@[simp] theorem Circuit.eval_snocLine_last (c : Circuit σ n k) (line : Line σ n c.size)
    (I : Interpretation σ U) (x : Fin n → U) :
    (c.snocLine line).eval I x (Fin.last k) = line.eval I x (c.program.eval I x) := by
  change (c.program.gate line).trace I x ((c.snocLine line).outputs (Fin.last k)) = _
  rw [outputs_snocLine_last]
  exact Program.eval_gate_last c.program line I x

/-- The earlier outputs keep their depths. -/
@[simp] theorem Circuit.outputDepths_snocLine_castSucc (c : Circuit σ n k)
    (line : Line σ n c.size) (t : Fin k) :
    (c.snocLine line).outputDepths t.castSucc = c.outputDepths t := by
  change (c.program.gate line).wireDepths ((c.snocLine line).outputs t.castSucc) =
    c.program.wireDepths (c.outputs t)
  rw [outputs_snocLine_castSucc, Program.wireDepths_gate_castSucc]

/-- The new last output has the depth of `line` over the wire depths of `c`. -/
@[simp] theorem Circuit.outputDepths_snocLine_last (c : Circuit σ n k)
    (line : Line σ n c.size) :
    (c.snocLine line).outputDepths (Fin.last k) = line.depth c.program.wireDepths := by
  change (c.program.gate line).wireDepths ((c.snocLine line).outputs (Fin.last k)) = _
  rw [outputs_snocLine_last]
  exact Program.depths_gate_last c.program line

end Cslib.Circuits
