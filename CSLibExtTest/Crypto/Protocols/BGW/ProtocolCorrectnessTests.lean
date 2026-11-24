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
open CSLibExt.Crypto.Protocols.BGW

namespace CSLibExtTest.Crypto.Protocols.BGW

/-- Seven is prime, so `ZMod 7` is a field. -/
instance testFactPrime7Protocol : Fact (Nat.Prime 7) := ⟨by norm_num⟩

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

/-- Explicit recombination vector for the independent concrete test. -/
def nzLam : Fin 3 → ZMod 7 :=
  fun i => if i.val = 0 then 3 else if i.val = 1 then 4 else 1

theorem mulCirc_program : mulCirc.program = mulProg := rfl

theorem mulCirc_outputs_zero :
    mulCirc.outputs (Fin.last 0) = Wire.gate (Fin.last 0 : Fin 1) := rfl

theorem mulLine_op : mulLine.op = ArithOp.mul := rfl

theorem mulLine_wires_zero : mulLine.wires (0 : Fin 2) = Wire.input 0 := rfl

theorem mulLine_wires_one : mulLine.wires (1 : Fin 2) = Wire.input 1 := rfl

theorem fin_one_zero_last : (0 : Fin 1) = Fin.last 0 := rfl

theorem params7_point (i : Fin 3) :
    params7.point i = ((i.val + 1 : ℕ) : ZMod 7) := rfl

/-- The threshold-one tail polynomial is the constant polynomial on its single
coefficient. -/
theorem tailPolynomial_one (coeffs : Fin 1 → ZMod 7) :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial
      (F := ZMod 7) 1 coeffs = Polynomial.C (coeffs 0) := by
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [Polynomial.coeff_C_zero]
    exact Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_coeff
      (F := ZMod 7) 1 coeffs ⟨0, Nat.zero_lt_succ 0⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hdeg :=
      Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial_degree_lt
        (F := ZMod 7) 1 coeffs
    have hle : ((1 : ℕ) : WithBot ℕ) ≤ ((m.succ : ℕ) : WithBot ℕ) := by
      exact_mod_cast (show 1 ≤ m.succ from by omega)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg hle)]
    show (0 : ZMod 7) = (Polynomial.C _).coeff (m + 1)
    exact Polynomial.coeff_C_succ.symm

/-- The threshold-one tail polynomial, stated at `params7.threshold` for
rewriting. -/
theorem tailPolynomial_params7 (coeffs : Fin params7.threshold → ZMod 7) :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.tailPolynomial
      (F := ZMod 7) params7.threshold coeffs =
      Polynomial.C (coeffs ⟨0, by decide⟩) :=
  tailPolynomial_one coeffs

/-- Closed form for shares in the `ZMod 7` test setup: the secret plus the
point times the single tail coefficient. -/
theorem share_params7_eq (coeffs : Fin params7.threshold → ZMod 7) (s : ZMod 7)
    (i : Fin 3) :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.share params7 coeffs s i =
      s + params7.point i * coeffs ⟨0, by decide⟩ := by
  simp only [Cslib.Crypto.Protocols.SecretSharing.Shamir.share,
    Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.sharingPolynomial_eval]
  rw [tailPolynomial_params7, Polynomial.eval_C]

/-- Independent concrete check of share-level execution: exact per-party output
shares for single-gate multiplication over `ZMod 7` with explicit nonzero
tapes and recombination vector. This does not invoke `protocol_correct` or
`protocol_correct_exists`. -/
theorem test_mul_concrete_shares :
    protoShares params7 nzLam mulCirc nzX nzTapeIn nzTapeMul 0
        ⟨⟨0, by decide⟩, Finset.mem_univ _⟩ = 2 ∧
      protoShares params7 nzLam mulCirc nzX nzTapeIn nzTapeMul 0
        ⟨⟨1, by decide⟩, Finset.mem_univ _⟩ = 5 ∧
      protoShares params7 nzLam mulCirc nzX nzTapeIn nzTapeMul 0
        ⟨⟨2, by decide⟩, Finset.mem_univ _⟩ = 1 := by
  refine ⟨?_, ?_⟩ <;>
    simp only [protoShares, execShare, mulCirc_program, fin_one_zero_last,
      mulCirc_outputs_zero, mulProg, gateShares, mulLine_op, newGateShare,
      mulLine_wires_zero, mulLine_wires_one, Wire.elim_input, inputShares,
      share_params7_eq, nzX, nzTapeIn, nzTapeMul, nzLam] <;>
    decide

/-- The exact shares from `test_mul_concrete_shares` reconstruct to the true
product `2 * 3 = 6`. This does not invoke `protocol_correct` or
`protocol_correct_exists`. -/
theorem test_mul_concrete_reconstruct :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct params7 Finset.univ
      (protoShares params7 nzLam mulCirc nzX nzTapeIn nzTapeMul 0) = 6 := by
  have hσ : (protoShares params7 nzLam mulCirc nzX nzTapeIn nzTapeMul 0) =
      fun (i : ↥(Finset.univ : Finset (Fin 3))) =>
        (Polynomial.C 6 + Polynomial.C 3 * Polynomial.X :
          Polynomial (ZMod 7)).eval (params7.point i) := by
    funext i
    match hm : i.1.val with
    | 0 =>
        have hi : i = (⟨⟨0, by decide⟩, Finset.mem_univ _⟩ :
          ↥(Finset.univ : Finset (Fin 3))) := Subtype.ext (Fin.ext hm)
        subst hi
        rw [test_mul_concrete_shares.1]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, params7_point]
        decide
    | 1 =>
        have hi : i = (⟨⟨1, by decide⟩, Finset.mem_univ _⟩ :
          ↥(Finset.univ : Finset (Fin 3))) := Subtype.ext (Fin.ext hm)
        subst hi
        rw [test_mul_concrete_shares.2.1]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, params7_point]
        decide
    | 2 =>
        have hi : i = (⟨⟨2, by decide⟩, Finset.mem_univ _⟩ :
          ↥(Finset.univ : Finset (Fin 3))) := Subtype.ext (Fin.ext hm)
        subst hi
        rw [test_mul_concrete_shares.2.2]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, params7_point]
        decide
    | Nat.succ (Nat.succ (Nat.succ n)) =>
        have := i.1.2
        omega
  have hx : Function.Injective
      (fun i : ↥(Finset.univ : Finset (Fin 3)) => params7.point i) := by
    intro i j hij
    exact Subtype.ext (params7.point_injective hij)
  have hcard3 : Fintype.card ↥(Finset.univ : Finset (Fin 3)) = 3 := by simp
  have h1 : (Polynomial.C 6 + Polynomial.C 3 * Polynomial.X :
      Polynomial (ZMod 7)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [max_le_iff]
    constructor
    · rw [Polynomial.natDegree_C]
      exact Nat.zero_le 1
    · calc (Polynomial.C 3 * Polynomial.X : Polynomial (ZMod 7)).natDegree
          ≤ Polynomial.X.natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = 1 := Polynomial.natDegree_X
  have hdeg : (Polynomial.C 6 + Polynomial.C 3 * Polynomial.X :
      Polynomial (ZMod 7)).degree <
      Fintype.card ↥(Finset.univ : Finset (Fin 3)) := by
    rw [hcard3]
    refine lt_trans (polyDegree_lt_succ_of_natDegree_le _ _ h1) ?_
    exact_mod_cast (show (1:ℕ) + 1 < 3 from by decide)
  have hcc : (Polynomial.C 6 + Polynomial.C 3 * Polynomial.X :
      Polynomial (ZMod 7)).constantCoeff = 6 := by
    simp only [Polynomial.constantCoeff_apply, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero]
    decide
  rw [hσ]
  unfold Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct
  exact (Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq
    (x := fun i : ↥(Finset.univ : Finset (Fin 3)) => params7.point i) hx hdeg).trans hcc

#print axioms test_mul_exists
#print axioms test_two_gate_exists
#print axioms test_mul_nonzero_tape
#print axioms test_mul_concrete_shares
#print axioms test_mul_concrete_reconstruct
#print axioms protocol_correct_exists

end CSLibExtTest.Crypto.Protocols.BGW
