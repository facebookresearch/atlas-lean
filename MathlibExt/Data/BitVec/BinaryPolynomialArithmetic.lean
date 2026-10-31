/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
execute multiplication and powering of fixed-width binary polynomial residues.
-/
module

public import MathlibExt.RingTheory.AdjoinRoot.BitVec

/-! # Executable binary polynomial modular arithmetic

The operations in this file use fixed-width shifts, xor, and the little-endian source folds from
the ETH formalization. They compute in the quotient by `X ^ s + g` without requiring that the
modulus be irreducible.
-/

@[expose] public section

namespace BitVec

/-- Multiply a binary residue by `X`, reducing by `X ^ s + g` when its top bit is set. -/
def mulXMod {s : Nat} (g w : BitVec s) : BitVec s :=
  if w.getMsbD 0 then w.shiftLeft 1 ^^^ g else w.shiftLeft 1

/-- Multiply binary residues by low-first Horner evaluation of the second operand's bits. -/
def mulMod {s t : Nat} (g x : BitVec s) (y : BitVec t) : BitVec s :=
  y.toBoolListLE.foldr
    (fun b c => if b then x ^^^ g.mulXMod c else g.mulXMod c) (0#s)

/-- Raise a binary residue to a natural power by repeated modular multiplication. -/
def powMod {s t : Nat} (g : BitVec s) (u : BitVec t) (e : Nat) : BitVec s :=
  (List.range e).foldl (fun c _ => g.mulMod c u) (1#s)

private theorem toPolynomial_shiftLeft_add_high {s : Nat} (w : BitVec s) :
    (w.shiftLeft 1).toPolynomial +
        (if w.getMsbD 0 then Polynomial.X ^ s else 0) =
      Polynomial.X * w.toPolynomial := by
  ext i
  rw [Polynomial.coeff_add]
  simp only [coeff_toPolynomial]
  by_cases hi : i = 0
  · subst i
    simp [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
      BitVec.getMsbD_eq_getLsbD]
    split
    · simp_all [Polynomial.coeff_X_pow]
      omega
    · simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [Polynomial.coeff_X_mul]
    rw [coeff_toPolynomial]
    by_cases hjs : j + 1 < s
    · have hs : 0 < s := by omega
      simp [BitVec.shiftLeft_eq,
        BitVec.getMsbD_eq_getLsbD, hjs, hs]
      rw [BitVec.getLsbD_eq_getElem (by omega)]
      split <;> simp_all
      all_goals split <;> simp_all [Polynomial.coeff_X_pow]
      all_goals omega
    · by_cases heq : j + 1 = s
      · subst s
        simp [BitVec.shiftLeft_eq,
          BitVec.getMsbD_eq_getLsbD]
        rw [← BitVec.getLsbD_eq_getElem (by omega)]
        generalize w.getLsbD j = b
        cases b <;> simp [Polynomial.coeff_X_pow]
      · have hge : s ≤ j := by omega
        rw [BitVec.getLsbD_of_ge w j hge]
        simp [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft,
          BitVec.getMsbD_eq_getLsbD, hjs, hge]
        split <;> simp_all [Polynomial.coeff_X_pow]

/-- Multiplication by `X` has its expected evaluation in every commutative ring receiving
`ZMod 2`. -/
theorem eval₂_mulXMod {s : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (g w : BitVec s)
    (hr : r ^ s = g.toPolynomial.eval₂ φ r) :
    (g.mulXMod w).toPolynomial.eval₂ φ r =
      r * w.toPolynomial.eval₂ φ r := by
  have hshift := congrArg (Polynomial.eval₂ φ r)
    (toPolynomial_shiftLeft_add_high w)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_mul] at hshift
  rw [mulXMod]
  split
  · rw [toPolynomial_xor, Polynomial.eval₂_add, ← hr]
    simpa [*, mul_comm] using hshift
  · simpa [*, mul_comm] using hshift

private def evalBits {R : Type*} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => (if b then 1 else 0) + r * evalBits r w

private theorem eval₂_ofBoolList {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (w : List Bool) :
    Polynomial.eval₂ φ r
        (Polynomial.ofCoeffList (w.map fun b => if b then (1 : ZMod 2) else 0)) =
      evalBits r w := by
  induction w with
  | nil => simp [evalBits]
  | cons b w ih =>
      rw [List.map_cons, Polynomial.ofCoeffList_cons, Polynomial.eval₂_add,
        Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, ih]
      cases b <;> simp [evalBits]

private theorem eval₂_toPolynomial {s : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (w : BitVec s) :
    w.toPolynomial.eval₂ φ r = evalBits r w.toBoolListLE := by
  simpa [toPolynomial] using eval₂_ofBoolList φ r w.toBoolListLE

private theorem zero_toPolynomial (s : Nat) : (0#s).toPolynomial = 0 := by
  ext i
  simp [coeff_toPolynomial]

private theorem eval₂_mulModAux {s : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (g x : BitVec s)
    (hr : r ^ s = g.toPolynomial.eval₂ φ r) (bits : List Bool) :
    (bits.foldr (fun b c => if b then x ^^^ g.mulXMod c else g.mulXMod c)
        (0#s)).toPolynomial.eval₂ φ r =
      x.toPolynomial.eval₂ φ r * evalBits r bits := by
  induction bits with
  | nil => simp [evalBits, zero_toPolynomial]
  | cons b bits ih =>
      simp only [List.foldr]
      cases b
      · rw [ite_eq_right (by simp), eval₂_mulXMod φ r g _ hr, ih]
        simp [evalBits]
        ring
      · rw [ite_eq_left (by simp), toPolynomial_xor, Polynomial.eval₂_add,
          eval₂_mulXMod φ r g _ hr, ih]
        simp [evalBits]
        ring

/-- Horner multiplication has its expected evaluation in every commutative ring receiving
`ZMod 2`; the second operand may have any width. -/
theorem eval₂_mulMod {s t : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (g x : BitVec s) (y : BitVec t)
    (hr : r ^ s = g.toPolynomial.eval₂ φ r) :
    (g.mulMod x y).toPolynomial.eval₂ φ r =
      x.toPolynomial.eval₂ φ r * y.toPolynomial.eval₂ φ r := by
  rw [mulMod]
  calc
    _ = x.toPolynomial.eval₂ φ r * evalBits r y.toBoolListLE :=
      eval₂_mulModAux φ r g x hr y.toBoolListLE
    _ = _ := by rw [← eval₂_toPolynomial φ r y]

private theorem one_toPolynomial {s : Nat} (hs : 0 < s) : (1#s).toPolynomial = 1 := by
  ext i
  rw [coeff_toPolynomial, BitVec.getLsbD_one, Polynomial.coeff_one]
  simp [hs]

private theorem powMod_succ {s t : Nat} (g : BitVec s) (u : BitVec t) (e : Nat) :
    g.powMod u (e + 1) = g.mulMod (g.powMod u e) u := by
  simp [powMod, List.range_succ]

/-- Repeated multiplication has its expected power evaluation for positive result width. -/
theorem eval₂_powMod {s t : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (g : BitVec s) (u : BitVec t) (e : Nat)
    (hs : 0 < s) (hr : r ^ s = g.toPolynomial.eval₂ φ r) :
    (g.powMod u e).toPolynomial.eval₂ φ r =
      (u.toPolynomial.eval₂ φ r) ^ e := by
  induction e with
  | zero => simp [powMod, one_toPolynomial hs]
  | succ e ih =>
      rw [show e + 1 = Nat.succ e by rfl, powMod_succ,
        eval₂_mulMod φ r g _ u hr, ih, pow_succ]

private theorem eval₂_adjoinRoot {s : Nat} (g : BitVec s)
    (p : Polynomial (ZMod 2)) :
    Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
        (AdjoinRoot.root g.monicModulus) p =
      AdjoinRoot.mk g.monicModulus p := by
  rw [← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

/-- Modular multiplication by `X` agrees with multiplication by the quotient root. -/
theorem adjoinRootEquiv_mulXMod {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv (g.mulXMod w) =
      AdjoinRoot.root g.monicModulus * g.adjoinRootEquiv w := by
  have hr : AdjoinRoot.root g.monicModulus ^ s =
      Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
        (AdjoinRoot.root g.monicModulus) g.toPolynomial := by
    rw [eval₂_adjoinRoot, ← adjoinRootEquiv_apply, adjoinRoot_root_pow]
  calc
    g.adjoinRootEquiv (g.mulXMod w) =
        Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) (g.mulXMod w).toPolynomial := by
      rw [eval₂_adjoinRoot, adjoinRootEquiv_apply]
    _ = AdjoinRoot.root g.monicModulus *
        Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) w.toPolynomial :=
      eval₂_mulXMod _ _ g w hr
    _ = _ := by rw [eval₂_adjoinRoot, ← adjoinRootEquiv_apply]

/-- Modular Horner multiplication agrees with multiplication in the polynomial quotient. -/
theorem adjoinRootEquiv_mulMod {s t : Nat} (g x : BitVec s) (y : BitVec t) :
    g.adjoinRootEquiv (g.mulMod x y) =
      g.adjoinRootEquiv x * AdjoinRoot.mk g.monicModulus y.toPolynomial := by
  have hr : AdjoinRoot.root g.monicModulus ^ s =
      Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
        (AdjoinRoot.root g.monicModulus) g.toPolynomial := by
    rw [eval₂_adjoinRoot, ← adjoinRootEquiv_apply, adjoinRoot_root_pow]
  calc
    g.adjoinRootEquiv (g.mulMod x y) =
        Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) (g.mulMod x y).toPolynomial := by
      rw [eval₂_adjoinRoot, adjoinRootEquiv_apply]
    _ = Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) x.toPolynomial *
        Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) y.toPolynomial :=
      eval₂_mulMod _ _ g x y hr
    _ = _ := by rw [eval₂_adjoinRoot, eval₂_adjoinRoot, ← adjoinRootEquiv_apply]

/-- Modular powering agrees with powering in the polynomial quotient, including width zero. -/
theorem adjoinRootEquiv_powMod {s t : Nat} (g : BitVec s) (u : BitVec t) (e : Nat) :
    g.adjoinRootEquiv (g.powMod u e) =
      (AdjoinRoot.mk g.monicModulus u.toPolynomial) ^ e := by
  by_cases hs : 0 < s
  · have hr : AdjoinRoot.root g.monicModulus ^ s =
        Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
          (AdjoinRoot.root g.monicModulus) g.toPolynomial := by
      rw [eval₂_adjoinRoot, ← adjoinRootEquiv_apply, adjoinRoot_root_pow]
    calc
      g.adjoinRootEquiv (g.powMod u e) =
          Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
            (AdjoinRoot.root g.monicModulus) (g.powMod u e).toPolynomial := by
        rw [eval₂_adjoinRoot, adjoinRootEquiv_apply]
      _ = (Polynomial.eval₂ (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus))
            (AdjoinRoot.root g.monicModulus) u.toPolynomial) ^ e :=
        eval₂_powMod _ _ g u e hs hr
      _ = _ := by rw [eval₂_adjoinRoot]
  · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    apply g.adjoinRootEquiv.symm.injective
    exact Subsingleton.elim _ _

end BitVec
