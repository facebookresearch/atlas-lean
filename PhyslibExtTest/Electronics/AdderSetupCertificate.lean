/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.AdderSetupCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Setup-certificate tests for the ripple-carry and carry-lookahead adders

Unequal per-gate delays `1/4, 1/2, 3/4` (cycling, so `D = 3/4`) and unequal
input arrivals `1/2, 1/4` (so `tq = 1/2`) certify setup on the 1- and 2-bit
ripple-carry adders and the 2-bit carry-lookahead adders. Under uniform delays
the 2-bit ripple-carry adder computes `3 + 1 + 0` correctly yet violates setup
once the period drops below the certificate, and the same holds for the 2-bit,
1-level carry-lookahead adder. Inputs that settle before `tq` meet setup
below the certificate, so exactness needs every input to arrive exactly at
`tq`. Over the full binary Boolean basis, which also
offers constants, a constant-free circuit is exact under uniform delays, while
a single constant gate meets setup at a period the certificate rejects.
-/

@[expose] public section

namespace PhyslibExtTest.Electronics.AdderSetupCertificate

open Cslib.Circuits PhyslibExt.Electronics.AdderSetupCertificate

/-- Unequal gate delays cycling through `1/4, 1/2, 3/4`. -/
noncomputable def delays (g : ℕ) : Fin g → ℝ := fun j => ((j.val % 3 : ℕ) + 1 : ℝ) / 4

/-- Unequal input arrivals: `1/2` on even inputs, `1/4` on odd ones. -/
noncomputable def arrivals (m : ℕ) : Fin m → ℝ := fun i => if i.val % 2 = 0 then 1 / 2 else 1 / 4

lemma delays_nonneg (g : ℕ) (j : Fin g) : 0 ≤ delays g j := by
  unfold delays
  positivity

lemma delays_le (g : ℕ) (j : Fin g) : delays g j ≤ 3 / 4 := by
  have h : j.val % 3 ≤ 2 := by omega
  have h' : ((j.val % 3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h
  unfold delays
  linarith

lemma arrivals_le (m : ℕ) (i : Fin m) : arrivals m i ≤ 1 / 2 := by
  unfold arrivals
  split_ifs <;> norm_num

/-! ## Unequal delays: the certificate on both adders and two widths -/

/-- The generic certificate on the 1-bit ripple-carry adder, at its depth `3`:
`1/2 + 3/4 * 3 + 1/10 + 1/20 = 29/10`. -/
example : SetupMet (rippleCarryAdder 1) (delays _) (arrivals _) (1 / 10) (1 / 20) (29 / 10) :=
  setupMet_of_depth _ _ _ (1 / 2) (3 / 4) _ _ _ (by norm_num) (arrivals_le _)
    (delays_nonneg _) (delays_le _) (by rw [rippleCarryAdder_depth le_rfl]; norm_num)

/-- 1-bit ripple-carry adder, depth `2 * 1 + 1`. -/
example : SetupMet (rippleCarryAdder 1) (delays _) (arrivals _) (1 / 10) (1 / 20) (29 / 10) :=
  rippleCarryAdder_setupMet 1 le_rfl _ _ (1 / 2) (3 / 4) _ _ _ (by norm_num) (arrivals_le _)
    (delays_nonneg _) (delays_le _) (by norm_num)

/-- 2-bit ripple-carry adder, depth `2 * 2 + 1`: `1/2 + 3/4 * 5 + 3/20 = 22/5`. -/
example : SetupMet (rippleCarryAdder 2) (delays _) (arrivals _) (1 / 10) (1 / 20) (22 / 5) :=
  rippleCarryAdder_setupMet 2 (by norm_num) _ _ (1 / 2) (3 / 4) _ _ _ (by norm_num)
    (arrivals_le _) (delays_nonneg _) (delays_le _) (by norm_num)

/-- 2-bit carry-lookahead adder with one level, depth `2 * 1 + 3`. -/
example : SetupMet (CarryLookahead.carryLookaheadAdder 2 1) (delays _) (arrivals _)
    (1 / 10) (1 / 20) (22 / 5) :=
  carryLookaheadAdder_setupMet 2 1 le_rfl le_rfl _ _ (1 / 2) (3 / 4) _ _ _ (by norm_num)
    (arrivals_le _) (delays_nonneg _) (delays_le _) (by norm_num)

/-- 2-bit carry-lookahead adder at `claLevels 2 = 2` levels, depth
`2 * log₂ 2 + 5 = 7`: `1/2 + 3/4 * 7 + 3/20 = 59/10`. -/
example : SetupMet (CarryLookahead.carryLookaheadAdder 2 (CarryLookahead.claLevels 2))
    (delays _) (arrivals _) (1 / 10) (1 / 20) (59 / 10) := by
  have hlog : Nat.log2 2 = 1 := by decide +kernel
  exact carryLookaheadAdder_claLevels_setupMet 2 le_rfl _ _ (1 / 2) (3 / 4) _ _ _
    (by norm_num) (arrivals_le _) (delays_nonneg _) (delays_le _) (by rw [hlog]; norm_num)

/-! ## Uniform delays: a correct addition that violates setup -/

/-- The 2-bit ripple-carry adder computes `3 + 1 + 0 = 4`: sum bits `0, 0`
and carry out `1`. -/
lemma adc_three_one : BitVec.adc 3#2 1#2 false = (true, 0#2) := by
  simp [BitVec.adc_spec, BitVec.carry]

example : (rippleCarryAdder 2).eval arithInterpretation (rcaInput 3#2 1#2 false) 0 = false := by
  rw [show (0 : Fin (2 + 1)) = ⟨0, by omega⟩ from rfl,
    rippleCarryAdder_sum _ _ _ 0 (by omega), adc_three_one]
  simp

example : (rippleCarryAdder 2).eval arithInterpretation (rcaInput 3#2 1#2 false) 1 = false := by
  rw [show (1 : Fin (2 + 1)) = ⟨1, by omega⟩ from rfl,
    rippleCarryAdder_sum _ _ _ 1 (by omega), adc_three_one]
  simp

example : (rippleCarryAdder 2).eval arithInterpretation (rcaInput 3#2 1#2 false) 2 = true := by
  rw [show (2 : Fin (2 + 1)) = ⟨2, by omega⟩ from rfl, rippleCarryAdder_carry, adc_three_one]

/-- At the certificate boundary `T = 1/4 + 1/2 * 5 + 3/20 = 29/10` setup holds. -/
example : SetupMet (rippleCarryAdder 2) (fun _ => 1 / 2) (fun _ => 1 / 4)
    (1 / 10) (1 / 20) (29 / 10) :=
  (rippleCarryAdder_setupMet_uniform_iff 2 (by norm_num) _ _ _ _ _ (by norm_num)
    (by norm_num)).mpr (by norm_num)

/-- Just below the boundary, `T = 289/100`, the correct adder violates setup. -/
example : ¬ SetupMet (rippleCarryAdder 2) (fun _ => 1 / 2) (fun _ => 1 / 4)
    (1 / 10) (1 / 20) (289 / 100) := by
  rw [rippleCarryAdder_setupMet_uniform_iff 2 (by norm_num) _ _ _ _ _ (by norm_num)
    (by norm_num)]
  norm_num

/-- The 2-bit, 1-level carry-lookahead adder has the same depth `5`: setup
holds at `29/10` and fails at `289/100`. -/
example : SetupMet (CarryLookahead.carryLookaheadAdder 2 1) (fun _ => 1 / 2) (fun _ => 1 / 4)
    (1 / 10) (1 / 20) (29 / 10) :=
  (carryLookaheadAdder_setupMet_uniform_iff 2 1 le_rfl le_rfl _ _ _ _ _ (by norm_num)
    (by norm_num)).mpr (by norm_num)

example : ¬ SetupMet (CarryLookahead.carryLookaheadAdder 2 1) (fun _ => 1 / 2)
    (fun _ => 1 / 4) (1 / 10) (1 / 20) (289 / 100) := by
  rw [carryLookaheadAdder_setupMet_uniform_iff 2 1 le_rfl le_rfl _ _ _ _ _ (by norm_num)
    (by norm_num)]
  norm_num

/-- Inputs that only settle by `tq = 1/4`, here all at `0`, meet setup at
`T = 53/20` although the certificate `1/4 + 1/2 * 5 + 3/20 = 29/10` exceeds it:
exactness needs every input to arrive exactly at `tq`. -/
example : (∀ i : Fin (2 * 2 + 1), (fun _ => (0 : ℝ)) i ≤ 1 / 4) ∧
    SetupMet (rippleCarryAdder 2) (fun _ => 1 / 2) (fun _ => 0) (1 / 10) (1 / 20) (53 / 20) ∧
    ¬ (1 / 4 + 1 / 2 * ((2 * 2 + 1 : ℕ) : ℝ) + 1 / 10 + 1 / 20 ≤ 53 / 20) :=
  ⟨fun _ => by norm_num,
    (rippleCarryAdder_setupMet_uniform_iff 2 (by norm_num) _ _ _ _ _ (by norm_num)
      (by norm_num)).mpr (by norm_num),
    by norm_num⟩

/-! ## Uniform delays over a basis that also offers constants -/

/-- Binary AND in the full binary Boolean basis. -/
def andOp : (fullSignature 2 Bool).Op := FullOp.fn fun x => x 0 && x 1

/-- Two AND gates in a chain over the full binary Boolean basis: gate `0` reads
inputs `0` and `1`, gate `1` reads gate `0` and input `0`; the output is gate `1`. -/
def andChain : Circuit (fullSignature 2 Bool) 2 1 where
  size := 2
  program := (Program.empty.gate ⟨andOp, fun k => if k.val = 0 then .input 0 else .input 1⟩).gate
    ⟨andOp, fun k => if k.val = 0 then .gate 0 else .input 0⟩
  outputs _ := .gate 1

lemma andChain_noConstantGates : NoConstantGates andChain.program :=
  ⟨⟨trivial, by decide⟩, by decide⟩

lemma andChain_depth : andChain.depth = 2 := by decide +kernel

/-- Uniform delay `1/2`, inputs at `1/4`: setup holds at the certificate
`1/4 + 1/2 * 2 + 3/20 = 7/5` and fails just below it. -/
example : SetupMet andChain (fun _ => 1 / 2) (fun _ => 1 / 4) (1 / 10) (1 / 20) (7 / 5) := by
  rw [setupMet_uniform_iff_of_noConstantGates _ andChain_noConstantGates (by norm_num)
    _ _ _ _ _ (by norm_num) (by norm_num), andChain_depth]
  norm_num

example : ¬ SetupMet andChain (fun _ => 1 / 2) (fun _ => 1 / 4) (1 / 10) (1 / 20) (139 / 100) := by
  rw [setupMet_uniform_iff_of_noConstantGates _ andChain_noConstantGates (by norm_num)
    _ _ _ _ _ (by norm_num) (by norm_num), andChain_depth]
  norm_num

/-- A constant gate `true` in the full binary Boolean basis. -/
def trueLine : Line (fullSignature 2 Bool) 2 0 := ⟨FullOp.con true, Fin.elim0⟩

/-- One constant gate `true` driving the only output. -/
def constCircuit : Circuit (fullSignature 2 Bool) 2 1 where
  size := 1
  program := Program.empty.gate trueLine
  outputs _ := .gate 0

/-- The constant gate settles at its delay `1/2` alone, so setup holds at
`T = 7/10` although the certificate `1/4 + 1/2 * 1 + 3/20 = 9/10` exceeds it:
exactness needs the no-constant-gate premise. -/
example : SetupMet constCircuit (fun _ => 1 / 2) (fun _ => 1 / 4) (1 / 10) (1 / 20) (7 / 10) ∧
    ¬ (1 / 4 + 1 / 2 * (constCircuit.depth : ℝ) + 1 / 10 + 1 / 20 ≤ 7 / 10) := by
  have hdepth : constCircuit.depth = 1 := by decide +kernel
  refine ⟨fun o => ?_, by rw [hdepth]; norm_num⟩
  have harr : constCircuit.outputArrivals (fun _ => 1 / 2) (fun _ => 1 / 4) o = 1 / 2 := by
    obtain rfl : o = Fin.last 0 := Subsingleton.elim _ _
    exact (Program.arrivals_gate_last Program.empty trueLine (fun _ => (1 / 2 : ℝ))
      (fun _ => (1 / 4 : ℝ))).trans (Line.arrival_of_arity_eq_zero _ _ _ rfl)
  rw [harr]
  norm_num

end PhyslibExtTest.Electronics.AdderSetupCertificate
