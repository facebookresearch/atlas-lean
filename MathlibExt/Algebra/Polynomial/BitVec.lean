/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
encode fixed-width bitvectors as little-endian polynomials over `ZMod 2`.
-/
module

public import MathlibExt.Data.BitVec.BoolList
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD

/-! # Bitvectors as binary polynomials

This file identifies the least-significant bit of a fixed-width bitvector with the constant
coefficient of a polynomial over `ZMod 2`.

The construction is adapted from `polyW` in
`eth/proof/variables/VariableBound/Field/Alg.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Polynomial

/-- A polynomial built from a low-coefficient-first list has degree strictly less than the list
length, including for an empty list and over a trivial semiring. -/
theorem degree_ofCoeffList_lt {R : Type*} [Semiring R] (l : List R) :
    (ofCoeffList l).degree < (l.length : WithBot Nat) := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_ofCoeffList, List.getD_eq_default _ _ hi]

/-- Reconstruct a polynomial from any fixed-width list containing all its possibly nonzero
coefficients. -/
theorem ofCoeffList_ofFn_coeff {R : Type*} [Semiring R] (p : Polynomial R) (s : Nat)
    (h : p.degree < (s : WithBot Nat)) :
    ofCoeffList (List.ofFn fun i : Fin s => p.coeff i.val) = p := by
  ext i
  rw [coeff_ofCoeffList]
  by_cases hi : i < s
  · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    rw [degree_lt_iff_coeff_zero] at h
    exact (h i (Nat.le_of_not_gt hi)).symm

/-- Extract the lowest `s` binary coefficients of a polynomial as a fixed-width bitvector.
Coefficients at indices at least `s` are deliberately truncated. -/
noncomputable def toBitVec (s : Nat) (p : Polynomial (ZMod 2)) : BitVec s :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin s => decide (p.coeff i.val = 1))).cast
    List.length_ofFn

end Polynomial

namespace BitVec

/-- The polynomial over `ZMod 2` whose coefficient of `X ^ i` is the `i`-th least-significant
bit of `w`. -/
noncomputable def toPolynomial {s : Nat} (w : BitVec s) : Polynomial (ZMod 2) :=
  Polynomial.ofCoeffList (w.toBoolListLE.map fun b => if b then 1 else 0)

/-- Every coefficient of the polynomial encoding is the corresponding least-significant bit;
indices outside the fixed width have coefficient zero. -/
theorem coeff_toPolynomial {s : Nat} (w : BitVec s) (i : Nat) :
    w.toPolynomial.coeff i = if w.getLsbD i then 1 else 0 := by
  rw [toPolynomial, Polynomial.coeff_ofCoeffList]
  by_cases hi : i < s
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      BitVec.getElem_toBoolListLE]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      BitVec.getLsbD_of_ge w i (Nat.le_of_not_gt hi)]
    rfl

/-- Extracting the coefficients of an encoded word recovers the original fixed-width word. -/
@[simp] theorem toBitVec_toPolynomial {s : Nat} (w : BitVec s) :
    w.toPolynomial.toBitVec s = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Polynomial.toBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn, coeff_toPolynomial]
  generalize w.getLsbD i = b
  cases b <;> decide

end BitVec

namespace Polynomial

private theorem if_decide_eq_one_zmod_two (c : ZMod 2) :
    (if decide (c = 1) then 1 else 0) = c := by
  revert c
  decide

/-- A polynomial whose degree is below the selected width is recovered after coefficient
extraction and fixed-width encoding. -/
@[simp] theorem toPolynomial_toBitVec (s : Nat) (p : Polynomial (ZMod 2))
    (h : p.degree < (s : WithBot Nat)) : (p.toBitVec s).toPolynomial = p := by
  ext i
  rw [BitVec.coeff_toPolynomial]
  by_cases hi : i < s
  · rw [toBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
      if_decide_eq_one_zmod_two]
  · rw [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [degree_lt_iff_coeff_zero] at h
    exact (h i (Nat.le_of_not_gt hi)).symm

end Polynomial

namespace BitVec

/-- Polynomial encoding turns bitwise xor into addition over `ZMod 2`; this is not the carried
integer addition on bitvectors. -/
theorem toPolynomial_xor {s : Nat} (x y : BitVec s) :
    (x ^^^ y).toPolynomial = x.toPolynomial + y.toPolynomial := by
  ext i
  simp only [coeff_toPolynomial, Polynomial.coeff_add, BitVec.getLsbD_xor]
  generalize x.getLsbD i = xb
  generalize y.getLsbD i = yb
  cases xb <;> cases yb <;> decide

/-- The monic polynomial obtained by adjoining the width term `X ^ s` to the encoded lower
coefficients. -/
noncomputable def monicModulus {s : Nat} (g : BitVec s) : Polynomial (ZMod 2) :=
  Polynomial.X ^ s + g.toPolynomial

/-- The binary modulus associated to a fixed-width word is monic, including at width zero. -/
theorem monicModulus_monic {s : Nat} (g : BitVec s) : g.monicModulus.Monic := by
  apply Polynomial.monic_X_pow_add
  simpa [toPolynomial] using Polynomial.degree_ofCoeffList_lt
    (g.toBoolListLE.map fun b => if b then (1 : ZMod 2) else 0)

/-- The natural degree of the binary modulus is exactly the width of its lower coefficients. -/
theorem monicModulus_natDegree {s : Nat} (g : BitVec s) : g.monicModulus.natDegree = s := by
  rw [monicModulus, add_comm]
  exact (Polynomial.natDegree_add_eq_right_of_degree_lt (by
    rw [Polynomial.degree_X_pow]
    simpa [toPolynomial] using Polynomial.degree_ofCoeffList_lt
      (g.toBoolListLE.map fun b => if b then (1 : ZMod 2) else 0))).trans
    (Polynomial.natDegree_X_pow s)

end BitVec
