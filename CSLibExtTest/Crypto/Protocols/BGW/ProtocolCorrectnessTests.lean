/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.BGW.ProtocolCorrectness
public import Cslib.Computability.Circuit.Basic
public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime

/-!
# BGW examples over `ZMod 7`

Nonvacuity checks for `protocol_correct_exists`: a three-party threshold-one
instance over `ZMod 7`, a single-gate multiplication, and a two-gate
add-then-multiply circuit, each evaluated on concrete inputs.
-/

@[expose] public section

open Cslib.Circuits

/-- Seven is prime, so `ZMod 7` is a field. -/
instance testFactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Three parties over `ZMod 7` with threshold one. -/
def params7 : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params (ZMod 7) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point := fun i => ((i.val + 1 : ℕ) : ZMod 7)
  point_injective := by decide
  point_nonzero := by decide

/-- Twice the threshold is below the number of parties. -/
theorem params7_two_mul_lt : 2 * params7.threshold < Fintype.card (Fin 3) := by decide

/-- Input values for the multiplication test: `3 * 5 = 15 = 1` in `ZMod 7`. -/
def mulX : Fin 2 → ZMod 7 := fun k => if k.val = 0 then 3 else 5

/-- A single multiplication gate over two inputs. -/
def mulLine : Line arithSignature 2 0 where
  op := .mul
  wires := fun k => if k.val = 0 then Wire.input 0 else Wire.input 1

/-- The single-gate multiplication program. -/
def mulProg : Program arithSignature 2 1 := Program.empty.gate mulLine

/-- The single-gate multiplication circuit. -/
def mulCirc : Circuit arithSignature 2 1 where
  program := mulProg
  outputs := fun _ => Wire.gate 0

/-- All-zero input tape for the multiplication test. -/
def mulTapeIn : Fin 2 → Fin params7.threshold → ZMod 7 := fun _ _ => 0

/-- All-zero multiplication tape for the multiplication test. -/
def mulTapeMul : Fin mulCirc.size → Fin 3 → Fin params7.threshold → ZMod 7 :=
  fun _ _ _ => 0

/-- The multiplication circuit computes `3 * 5 = 1` in `ZMod 7`. -/
theorem test_mul_eval : (mulCirc.eval arithInterp mulX) 0 = 1 := rfl

/-- Nonvacuity: some recombination vector makes the three-party `ZMod 7`
    multiplication correct. -/
theorem test_mul_exists : ∃ lam : Fin 3 → ZMod 7,
    Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params7 Finset.univ
      (protoShares params7 lam mulCirc mulX mulTapeIn mulTapeMul 0) = 1 := by
  obtain ⟨lam, hlam⟩ := protocol_correct_exists params7 params7_two_mul_lt
  exact ⟨lam, (hlam mulCirc mulX mulTapeIn mulTapeMul 0).trans test_mul_eval⟩

/-- Input values for the two-gate test: `(3 + 5) * 3 = 3` in `ZMod 7`. -/
def addMulX : Fin 2 → ZMod 7 := fun k => if k.val = 0 then 3 else 5

/-- Addition of the two inputs. -/
def addLine : Line arithSignature 2 0 where
  op := .add
  wires := fun k => if k.val = 0 then Wire.input 0 else Wire.input 1

/-- Multiplication of the first gate with the first input. -/
def mulLine2 : Line arithSignature 2 1 where
  op := .mul
  wires := fun k => if k.val = 0 then Wire.gate 0 else Wire.input 0

/-- The two-gate add-then-multiply program. -/
def addMulProg : Program arithSignature 2 2 := (Program.empty.gate addLine).gate mulLine2

/-- The two-gate add-then-multiply circuit. -/
def addMulCirc : Circuit arithSignature 2 1 where
  program := addMulProg
  outputs := fun _ => Wire.gate 1

/-- All-zero input tape for the two-gate test. -/
def addMulTapeIn : Fin 2 → Fin params7.threshold → ZMod 7 := fun _ _ => 0

/-- All-zero multiplication tape for the two-gate test. -/
def addMulTapeMul : Fin addMulCirc.size → Fin 3 → Fin params7.threshold → ZMod 7 :=
  fun _ _ _ => 0

/-- The two-gate circuit computes `(3 + 5) * 3 = 3` in `ZMod 7`. -/
theorem test_two_gate_eval : (addMulCirc.eval arithInterp addMulX) 0 = 3 := rfl

/-- Nonvacuity: some recombination vector makes the three-party `ZMod 7`
    two-gate example correct. -/
theorem test_two_gate_exists : ∃ lam : Fin 3 → ZMod 7,
    Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params7 Finset.univ
      (protoShares params7 lam addMulCirc addMulX addMulTapeIn addMulTapeMul 0) = 3 := by
  obtain ⟨lam, hlam⟩ := protocol_correct_exists params7 params7_two_mul_lt
  exact ⟨lam, (hlam addMulCirc addMulX addMulTapeIn addMulTapeMul 0).trans
    test_two_gate_eval⟩

/-- Input values for the nonzero-tape test: `2 * 3 = 6` in `ZMod 7`. -/
def nzX : Fin 2 → ZMod 7 := fun k => if k.val = 0 then 2 else 3

/-- Nonzero input slopes for the nonzero-tape test. -/
def nzTapeIn : Fin 2 → Fin params7.threshold → ZMod 7 :=
  fun k _ => if k.val = 0 then 4 else 5

/-- Nonzero dealer slopes for the nonzero-tape test. -/
def nzTapeMul : Fin mulCirc.size → Fin 3 → Fin params7.threshold → ZMod 7 :=
  fun _ i _ => if i.val = 0 then 1 else if i.val = 1 then 2 else 6

/-- The multiplication circuit computes `2 * 3 = 6` in `ZMod 7`. -/
theorem test_mul_nz_eval : (mulCirc.eval arithInterp nzX) 0 = 6 := rfl

/-- Nonvacuity with nonzero tapes: some recombination vector makes the
    three-party `ZMod 7` multiplication correct. -/
theorem test_mul_nonzero_tape : ∃ lam : Fin 3 → ZMod 7,
    Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params7 Finset.univ
      (protoShares params7 lam mulCirc nzX nzTapeIn nzTapeMul 0) = 6 := by
  obtain ⟨lam, hlam⟩ := protocol_correct_exists params7 params7_two_mul_lt
  exact ⟨lam, (hlam mulCirc nzX nzTapeIn nzTapeMul 0).trans test_mul_nz_eval⟩

#print axioms test_mul_exists
#print axioms test_two_gate_exists
#print axioms test_mul_nonzero_tape
#print axioms protocol_correct_exists
