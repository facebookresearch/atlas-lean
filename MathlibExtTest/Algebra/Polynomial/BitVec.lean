/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Polynomial.BitVec
import Mathlib.Data.List.GetD

@[expose] public section

open Polynomial

namespace ETHBitVecPolynomialReference

/-- The source Boolean-to-ring embedding, local to the compatibility test. -/
private def sourceBit (R : Type) [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- The source little-endian Horner decoder, local to the compatibility test. -/
private def sourceDecR {R : Type} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => sourceBit R b + r * sourceDecR r w

/-- The exact source polynomial constructor. -/
private noncomputable def sourcePolyW (w : List Bool) : Polynomial (ZMod 2) :=
  sourceDecR X w

/-- The exact source monic modulus constructor. -/
private noncomputable def sourceModP (g : List Bool) : Polynomial (ZMod 2) :=
  X ^ g.length + sourcePolyW g

private theorem coeff_sourcePolyW (w : List Bool) (i : Nat) :
    (sourcePolyW w).coeff i = sourceBit (ZMod 2) (w.getD i false) := by
  induction w generalizing i with
  | nil => simp [sourcePolyW, sourceDecR, sourceBit]
  | cons b w ih =>
    have h : sourcePolyW (b :: w) = C (sourceBit (ZMod 2) b) + X * sourcePolyW w := by
      unfold sourcePolyW
      rw [sourceDecR]
      cases b <;> simp [sourceBit]
    rw [h, coeff_add]
    cases i with
    | zero => cases b <;> simp [sourceBit]
    | succ i => simp [coeff_X_mul, ih, coeff_C_succ]

/-- The new codec is the exact source coefficient-first constructor at every width. -/
example {s : Nat} (w : BitVec s) :
    w.toPolynomial = sourcePolyW w.toBoolListLE := by
  ext i
  rw [BitVec.coeff_toPolynomial, coeff_sourcePolyW, BitVec.getD_toBoolListLE]
  rfl

/-- The new modulus is the exact source modulus at every width. -/
example {s : Nat} (g : BitVec s) :
    g.monicModulus = sourceModP g.toBoolListLE := by
  rw [BitVec.monicModulus, sourceModP, BitVec.length_toBoolListLE]
  congr 1
  ext i
  rw [BitVec.coeff_toPolynomial, coeff_sourcePolyW, BitVec.getD_toBoolListLE]
  rfl

end ETHBitVecPolynomialReference

/-- The generic degree bound needs no nontriviality assumption. -/
example (l : List (ZMod 1)) :
    (ofCoeffList l).degree < (l.length : WithBot Nat) :=
  Polynomial.degree_ofCoeffList_lt l

example : (ofCoeffList ([] : List Int)).degree < (0 : WithBot Nat) :=
  Polynomial.degree_ofCoeffList_lt []

example : (ofCoeffList ([1, 0, 0] : List Int)).degree < (3 : WithBot Nat) :=
  Polynomial.degree_ofCoeffList_lt _

/-- Fixed-width coefficient reconstruction retains explicit high zero padding. -/
example {R : Type*} [Semiring R] (p : Polynomial R)
    (h : p.degree < (5 : WithBot Nat)) :
    ofCoeffList (List.ofFn fun i : Fin 5 => p.coeff i.val) = p :=
  Polynomial.ofCoeffList_ofFn_coeff p 5 h

/-- Both codec directions support width zero. -/
example : (BitVec.ofNat 0 0).toPolynomial = 0 := by
  simp [BitVec.toPolynomial, BitVec.toBoolListLE]

example : (0 : Polynomial (ZMod 2)).toBitVec 0 = BitVec.ofNat 0 0 := by
  decide

/-- A word's coefficients vanish immediately beyond its fixed width. -/
example {s : Nat} (w : BitVec s) : w.toPolynomial.coeff s = 0 := by
  rw [BitVec.coeff_toPolynomial, BitVec.getLsbD_of_ge w s (Nat.le_refl s)]
  rfl

/-- Both fixed-width roundtrips, including retained leading zeros. -/
example : ((BitVec.ofNat 5 6).toPolynomial.toBitVec 5) = BitVec.ofNat 5 6 := by
  rw [BitVec.toBitVec_toPolynomial]

example (p : Polynomial (ZMod 2)) (h : p.degree < (5 : WithBot Nat)) :
    (p.toBitVec 5).toPolynomial = p :=
  Polynomial.toPolynomial_toBitVec 5 p h

/-- Coefficients at and above the requested width are truncated. -/
example : ((X ^ 3 : Polynomial (ZMod 2)).toBitVec 3) = BitVec.ofNat 3 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Polynomial.toBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hne : i ≠ 3 := by omega
  simp [coeff_X_pow, hne]

/-- Xor cancellation is polynomial addition in characteristic two. -/
example {s : Nat} (w : BitVec s) : (w ^^^ w).toPolynomial = 0 := by
  rw [BitVec.toPolynomial_xor]
  ext i
  simp only [coeff_add, BitVec.coeff_toPolynomial, coeff_zero]
  generalize w.getLsbD i = b
  cases b <;> decide

/-- Builtin bitvector addition carries, while xor does not. -/
example : (BitVec.ofNat 2 1 + BitVec.ofNat 2 1) = BitVec.ofNat 2 2 := by decide
example : (BitVec.ofNat 2 1 ^^^ BitVec.ofNat 2 1) = BitVec.ofNat 2 0 := by decide

example : (BitVec.ofNat 2 1 + BitVec.ofNat 2 1).toPolynomial = X := by
  rw [show BitVec.ofNat 2 1 + BitVec.ofNat 2 1 = BitVec.ofNat 2 2 by decide]
  ext i
  rw [BitVec.coeff_toPolynomial, Polynomial.coeff_X]
  by_cases h0 : i = 0
  · subst i
    decide
  by_cases h1 : i = 1
  · subst i
    decide
  have hi : 2 ≤ i := by omega
  have h1' : 1 ≠ i := Ne.symm h1
  rw [BitVec.getLsbD_of_ge _ _ hi]
  simp [h1']

example : (BitVec.ofNat 2 1 ^^^ BitVec.ofNat 2 1).toPolynomial = 0 := by
  rw [show BitVec.ofNat 2 1 ^^^ BitVec.ofNat 2 1 = BitVec.ofNat 2 0 by decide]
  ext i
  rw [BitVec.coeff_toPolynomial]
  by_cases hi : 2 ≤ i
  · rw [BitVec.getLsbD_of_ge _ _ hi]
    rfl
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with h | h <;> subst i <;> simp

/-- The width-three word `6` has low-first bits `[false, true, true]`. -/
example : (BitVec.ofNat 3 6).toBoolListLE = [false, true, true] := by decide

example : (BitVec.ofNat 3 6).toPolynomial = X + X ^ 2 := by
  ext i
  rw [BitVec.coeff_toPolynomial, coeff_add, coeff_X_pow, Polynomial.coeff_X]
  by_cases h0 : i = 0
  · subst i
    decide
  by_cases h1 : i = 1
  · subst i
    decide
  by_cases h2 : i = 2
  · subst i
    decide
  have hi : 3 ≤ i := by omega
  have h1' : 1 ≠ i := Ne.symm h1
  rw [BitVec.getLsbD_of_ge _ _ hi]
  simp [h1', h2]

/-- Width-zero and width-one monic moduli. -/
example : (BitVec.ofNat 0 0).monicModulus = 1 := by
  simp [BitVec.monicModulus, BitVec.toPolynomial, BitVec.toBoolListLE]

example : (BitVec.ofNat 1 0).monicModulus = X := by
  simp [BitVec.monicModulus, BitVec.toPolynomial, BitVec.toBoolListLE]

/-- The populated source example has coefficients `1 + X + X³`. -/
example : (BitVec.ofNat 3 3).monicModulus = X ^ 3 + X + 1 := by
  ext i
  rw [BitVec.monicModulus, coeff_add, coeff_add, coeff_X_pow,
    BitVec.coeff_toPolynomial]
  by_cases h0 : i = 0
  · subst i
    simp [coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
  by_cases h1 : i = 1
  · subst i
    simp [coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
  by_cases h2 : i = 2
  · subst i
    simp [coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
  by_cases h3 : i = 3
  · subst i
    simp [coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
  have hi : 3 ≤ i := by omega
  have h1' : 1 ≠ i := Ne.symm h1
  rw [BitVec.getLsbD_of_ge _ _ hi]
  simp [coeff_add, Polynomial.coeff_X, Polynomial.coeff_one, h0, h1', h3]

example : (BitVec.ofNat 3 3).monicModulus.Monic :=
  BitVec.monicModulus_monic _

example : (BitVec.ofNat 3 3).monicModulus.natDegree = 3 :=
  BitVec.monicModulus_natDegree _

#print axioms Polynomial.degree_ofCoeffList_lt
#print axioms Polynomial.ofCoeffList_ofFn_coeff
#print axioms BitVec.toPolynomial
#print axioms Polynomial.toBitVec
#print axioms BitVec.coeff_toPolynomial
#print axioms BitVec.toBitVec_toPolynomial
#print axioms Polynomial.toPolynomial_toBitVec
#print axioms BitVec.toPolynomial_xor
#print axioms BitVec.monicModulus
#print axioms BitVec.monicModulus_monic
#print axioms BitVec.monicModulus_natDegree
