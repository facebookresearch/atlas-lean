/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.AnnotatedArrival
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! Tests for `Circuit.outputArrivals` and its depth bound, on a four-gate circuit over CSLib's
`fullSignature 2 Bool` (binary gates and constants): a constant gate, a gate that fans out to two
gates and an output, unequal delays, and an input wired straight to an output. Its arrival times
are computed, the bounds are instantiated and checked against them, a chain with negative delays
meets the bound for `D = 0`, and two boundary probes show that the premises `0 ≤ D` and `0 ≤ a0`
cannot be dropped. -/

namespace Cslib.Circuits

/-- Binary gates and constants over `Bool`. -/
private abbrev σ2 : Signature := fullSignature 2 Bool

/-- A constant gate. -/
private def conLine {n g : ℕ} (b : Bool) : Line σ2 n g := ⟨FullOp.con b, Fin.elim0⟩

/-- A binary AND gate reading `u` and `v`. -/
private def andLine {n g : ℕ} (u v : Wire n g) : Line σ2 n g :=
  ⟨FullOp.fn (fun f => f 0 && f 1), ![u, v]⟩

private theorem arity_fn (f : (Fin 2 → Bool) → Bool) : σ2.Arity (FullOp.fn f) = 2 := rfl

private theorem arity_con (b : Bool) : σ2.Arity (FullOp.con b) = 0 := rfl

/-- An AND gate arrives at its delay plus the maximum, from `0`, of its two fan-in arrivals. -/
private theorem andLine_arrival {n g : ℕ} (u v : Wire n g) (A : Wire n g → ℝ) (d : ℝ) :
    (andLine u v).arrival A d = d + max (max 0 (A u)) (A v) := by
  simp only [Line.arrival, andLine, arity_fn, Fin.foldl_succ, Fin.foldl_zero]
  simp

/-- The constant-node convention: a constant gate arrives at its delay, whatever the arrival
times of the wires around it. -/
private theorem conLine_arrival {n g : ℕ} (b : Bool) (A : Wire n g → ℝ) (d : ℝ) :
    (conLine b).arrival A d = d :=
  Line.arrival_of_arity_eq_zero _ A d (arity_con b)

/-- Two inputs; `g0` constant, `g1 = and(input 0, g0)`, `g2 = and(g1, input 1)`,
`g3 = and(g1, g2)`. `g1` fans out to `g2`, `g3` and an output. Gate references are written with
`Fin.last` and `Fin.castSucc`, the form the structural equations of `Program.arrivals` use. -/
private def prog : Program σ2 2 4 :=
  (((Program.empty.gate (conLine true)).gate (andLine (.input 0) (.gate (Fin.last 0)))).gate
    (andLine (.gate (Fin.last 1)) (.input 1))).gate
      (andLine (.gate (Fin.last 1).castSucc) (.gate (Fin.last 2)))

/-- Outputs `g3`, `g1`, `g0` and `input 1`. -/
private def outs : Fin 4 → Wire 2 4 :=
  ![.gate (Fin.last 3), .gate (Fin.last 1).castSucc.castSucc,
    .gate (Fin.last 0).castSucc.castSucc.castSucc, .input 1]

private def circ : Circuit σ2 2 4 := ⟨prog, outs⟩

/-- Unequal delays `1/4, 3/2, 1/2, 1/4` on `g0, …, g3`. -/
private noncomputable def delays (j : Fin 4) : ℝ :=
  if j.val = 0 then 1/4 else if j.val = 1 then 3/2 else if j.val = 2 then 1/2 else 1/4

/-- Both inputs arrive at `1/2`. -/
private noncomputable def inputs : Fin 2 → ℝ := fun _ => 1/2

/-- Depths: `g3` has `4`, `g1` has `2`, the constant `g0` has `1`, the input has `0`. -/
private theorem circ_outputDepths : circ.outputDepths = ![4, 2, 1, 0] := by decide

private theorem circ_depth : circ.depth = 4 := by decide

/-- Arrivals: `g0 = 1/4` (the constant at its delay), `g1 = max(1/2, 1/4) + 3/2 = 2`,
`g2 = max(2, 1/2) + 1/2 = 5/2`, `g3 = max(2, 5/2) + 1/4 = 11/4`; the input output arrives at
`1/2`. -/
private theorem circ_outputArrivals :
    circ.outputArrivals delays inputs = ![11/4, 2, 1/4, 1/2] := by
  funext o
  change prog.wireArrivals delays inputs (outs o) = _
  fin_cases o <;>
  · simp only [outs, prog, Program.wireArrivals, Wire.elim, Program.arrivals_gate_last,
      Program.arrivals_gate_castSucc, andLine_arrival, conLine_arrival,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    norm_num [delays, inputs]

private theorem delays_nonneg : ∀ j, 0 ≤ delays j := by
  intro j; fin_cases j <;> norm_num [delays]

private theorem delays_le : ∀ j, delays j ≤ 3/2 := by
  intro j; fin_cases j <;> norm_num [delays]

/-- The bound at `a0 = 1/2`, `D = 3/2`, from the theorem. -/
example (o : Fin 4) :
    circ.outputArrivals delays inputs o ≤ 1/2 + 3/2 * (circ.outputDepths o : ℝ) :=
  Circuit.outputArrivals_le_add_mul_outputDepths circ delays inputs (1/2) (3/2) (by norm_num)
    (fun _ => le_rfl) delays_nonneg delays_le o

/-- The computed values against the bound: `11/4 ≤ 1/2 + 3/2 * 4`, `2 ≤ 1/2 + 3/2 * 2`,
`1/4 ≤ 1/2 + 3/2 * 1`, and `1/2 = 1/2 + 3/2 * 0` at the input, where the bound is tight. -/
example : List.ofFn (fun o => 1/2 + 3/2 * (circ.outputDepths o : ℝ) -
    circ.outputArrivals delays inputs o) = [15/4, 3/2, 7/4, 0] := by
  rw [circ_outputArrivals, circ_outputDepths]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- The settling-time bound: every output arrives by `1/2 + 3/2 * 4`. -/
example (o : Fin 4) : circ.outputArrivals delays inputs o ≤ 1/2 + 3/2 * 4 := by
  have h := Circuit.outputArrivals_le_add_mul_depth circ delays inputs (1/2) (3/2)
    (by norm_num) (fun _ => le_rfl) delays_nonneg delays_le o
  rwa [circ_depth, Nat.cast_ofNat] at h

/-! Negative delays under a nonnegative bound, then boundary probes: dropping either premise
breaks the bound. -/

/-- A chain of two AND gates over one input. -/
private def chainProg : Program σ2 1 2 :=
  (Program.empty.gate (andLine (.input 0) (.input 0))).gate
    (andLine (.gate (Fin.last 0)) (.gate (Fin.last 0)))

/-- The chain as a circuit with the last gate as output, of depth `2`. -/
private def chain : Circuit σ2 1 1 := ⟨chainProg, fun _ => .gate (Fin.last 1)⟩

private theorem chain_outputDepths : chain.outputDepths 0 = 2 := by decide

/-- With every delay `-1` and inputs at `0`, the output arrives at `-1`. -/
private theorem chain_outputArrivals_neg :
    chain.outputArrivals (fun _ => -1) (fun _ => 0) 0 = -1 := by
  change chainProg.wireArrivals (fun _ => -1) (fun _ => 0) (.gate (Fin.last 1)) = _
  simp only [chainProg, Program.wireArrivals, Wire.elim, Program.arrivals_gate_last,
    andLine_arrival]
  norm_num

/-- Negative delays are allowed when the bound is nonnegative: delays `-1`, `D = 0` and
`a0 = 0` give `-1 ≤ 0 + 0 * 2`, from the theorem. -/
example : chain.outputArrivals (fun _ => -1) (fun _ => 0) 0 ≤
    0 + 0 * (chain.outputDepths 0 : ℝ) :=
  Circuit.outputArrivals_le_add_mul_outputDepths_of_nonneg_bound chain (fun _ => -1)
    (fun _ => 0) 0 0 le_rfl (fun _ => le_rfl) le_rfl (fun _ => by norm_num) 0

/-- The same instance against the circuit-depth bound, checked on the computed value. -/
example : chain.outputArrivals (fun _ => -1) (fun _ => 0) 0 ≤ 0 + 0 * (chain.depth : ℝ) ∧
    chain.outputArrivals (fun _ => -1) (fun _ => 0) 0 = -1 :=
  ⟨Circuit.outputArrivals_le_add_mul_depth_of_nonneg_bound chain (fun _ => -1) (fun _ => 0)
    0 0 le_rfl (fun _ => le_rfl) le_rfl (fun _ => by norm_num) 0, chain_outputArrivals_neg⟩

/-- Delays `-1` with the negative bound `D = -1` and input time `a0 = 0`: the output arrives
at `-1`, later than `0 + (-1) * 2`, so `0 ≤ D` cannot be dropped. -/
example : ¬ chain.outputArrivals (fun _ => -1) (fun _ => 0) 0 ≤
    0 + (-1) * (chain.outputDepths 0 : ℝ) := by
  rw [chain_outputDepths]
  change ¬ chainProg.wireArrivals (fun _ => -1) (fun _ => 0) (.gate (Fin.last 1)) ≤ _
  simp only [chainProg, Program.wireArrivals, Wire.elim, Program.arrivals_gate_last,
    andLine_arrival]
  norm_num

/-- Zero delays and inputs at `a0 = -1`: arrival times are measured from the origin, so the
output arrives at `0`, later than `-1 + 0 * 2`. -/
example : ¬ chain.outputArrivals (fun _ => 0) (fun _ => -1) 0 ≤
    -1 + 0 * (chain.outputDepths 0 : ℝ) := by
  change ¬ chainProg.wireArrivals (fun _ => 0) (fun _ => -1) (.gate (Fin.last 1)) ≤ _
  simp only [chainProg, Program.wireArrivals, Wire.elim, Program.arrivals_gate_last,
    andLine_arrival]
  norm_num

#print axioms Circuit.outputArrivals_le_add_mul_outputDepths
#print axioms Circuit.outputArrivals_le_add_mul_depth
#print axioms Program.wireArrivals_le_add_mul_wireDepths
#print axioms Circuit.outputArrivals_le_add_mul_outputDepths_of_nonneg_bound
#print axioms Circuit.outputArrivals_le_add_mul_depth_of_nonneg_bound
#print axioms Program.wireArrivals_le_add_mul_wireDepths_of_nonneg_bound

end Cslib.Circuits
