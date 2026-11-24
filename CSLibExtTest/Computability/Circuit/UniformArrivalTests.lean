/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.UniformArrival
public import CSLibExt.Computability.Circuit.Arithmetic.RippleCarry
import Mathlib.Tactic.NormNum

/-! Tests for exact arrival times under uniform gate delays. With uniform delay `1/2` and inputs
at `1/4`, the outputs of the 2-bit ripple-carry adder arrive at `1/4` plus `1/2` times their depths
`2` and `5`. Over the full binary Boolean basis, which also offers constants, the signature-wide
premise fails, yet a two-gate AND chain has no constant gate and its output arrives exactly at
`1/4 + 1/2 * 2`, attaining the circuit depth. A single constant gate arrives at its delay `1/2`,
before `1/4 + 1/2 * 1`, so the no-constant-gate premise cannot be dropped. -/

namespace Cslib.Circuits

/-! ## A signature without constants -/

example : (rippleCarryAdder 2).outputArrivals (fun _ => 1 / 2) (fun _ => 1 / 4) 2 = 11 / 4 := by
  have hdepth : (rippleCarryAdder 2).outputDepths 2 = 5 := by decide +kernel
  rw [Circuit.outputArrivals_uniform (fun _ => two_pos) _ _ _ (by norm_num) (by norm_num),
    hdepth]
  norm_num

example : (rippleCarryAdder 2).outputArrivals (fun _ => 1 / 2) (fun _ => 1 / 4) 0 = 5 / 4 := by
  have hdepth : (rippleCarryAdder 2).outputDepths 0 = 2 := by decide +kernel
  rw [Circuit.outputArrivals_uniform (fun _ => two_pos) _ _ _ (by norm_num) (by norm_num),
    hdepth]
  norm_num

/-! ## A signature that also offers constants -/

/-- Binary AND in the full binary Boolean basis. -/
private def andOp : (fullSignature 2 Bool).Op := FullOp.fn fun x => x 0 && x 1

/-- Two AND gates in a chain: gate `0` reads inputs `0` and `1`, gate `1` reads gate `0` and
input `0`; the output is gate `1`. -/
private def andChain : Circuit (fullSignature 2 Bool) 2 1 where
  size := 2
  program := (Program.empty.gate ⟨andOp, fun k => if k.val = 0 then .input 0 else .input 1⟩).gate
    ⟨andOp, fun k => if k.val = 0 then .gate 0 else .input 0⟩
  outputs _ := .gate 1

/-- The basis offers constants, so the signature-wide premise fails. -/
example : ¬ ∀ op, 0 < (fullSignature 2 Bool).Arity op := fun h =>
  absurd (h (.con true)) (by decide)

private theorem andChain_noConstantGates : andChain.program.NoConstantGates :=
  ⟨⟨trivial, by decide⟩, by decide⟩

private theorem andChain_depth : andChain.depth = 2 := by decide +kernel

/-- The only output attains the circuit depth `2`. -/
example : ∃ o, andChain.outputDepths o = andChain.depth :=
  andChain.exists_outputDepths_eq_depth (by norm_num)

/-- The chain's output arrives exactly at `1/4 + 1/2 * 2 = 5/4`. -/
example : andChain.outputArrivals (fun _ => 1 / 2) (fun _ => 1 / 4) 0 = 5 / 4 := by
  have hdepth : andChain.outputDepths 0 = 2 := by decide +kernel
  rw [andChain.outputArrivals_uniform_of_noConstantGates andChain_noConstantGates _ _
    (by norm_num) (by norm_num), hdepth]
  norm_num

/-- A constant gate `true` in the full binary Boolean basis. -/
private def trueLine : Line (fullSignature 2 Bool) 2 0 := ⟨FullOp.con true, Fin.elim0⟩

/-- One constant gate `true` driving the only output. -/
private def constCircuit : Circuit (fullSignature 2 Bool) 2 1 where
  size := 1
  program := Program.empty.gate trueLine
  outputs _ := .gate 0

/-- The constant gate has depth `1` but arrives at its delay `1/2`, before
`1/4 + 1/2 * 1 = 3/4`: exactness needs the no-constant-gate premise. -/
example : constCircuit.outputArrivals (fun _ => 1 / 2) (fun _ => 1 / 4) 0 = 1 / 2 ∧
    (1 / 2 : ℝ) < 1 / 4 + 1 / 2 * (constCircuit.outputDepths 0 : ℝ) := by
  have hdepth : constCircuit.outputDepths 0 = 1 := by decide +kernel
  refine ⟨?_, by rw [hdepth]; norm_num⟩
  exact (Program.arrivals_gate_last Program.empty trueLine (fun _ => (1 / 2 : ℝ))
    (fun _ => (1 / 4 : ℝ))).trans (Line.arrival_of_arity_eq_zero _ _ _ rfl)

end Cslib.Circuits
