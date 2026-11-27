/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.SOSCertificate
public meta import MathlibExt.Analysis.Numerical.SOSCertificate
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Fin

/-! Tests for Gram-matrix sum-of-squares certificates: a satisfiable degree-2
instance, use of the PSD hypothesis, boundary cases, and axiom checks. -/

open scoped BigOperators Matrix

/-- Test 1 (satisfiable instance): `p = x^2 - 2xy + 2y^2` is the Gram polynomial
of `Q = !![1, -1; -1, 2]`, which is PSD, hence `p` is nonnegative at `(1, 1)`. -/
example : 0 ≤ (MvPolynomial.X 0 ^ 2 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1
    + 2 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) Rat).eval₂ (Rat.castHom Real)
    ![1, 1] := by
  have hQ : ((!![1, -1; -1, 2] : Matrix (Fin 2) (Fin 2) Rat)).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · unfold Matrix.IsHermitian
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x
      have h : star x ⬝ᵥ ((!![1, -1; -1, 2] : Matrix (Fin 2) (Fin 2) Rat) *ᵥ x)
          = (x 0 - x 1) ^ 2 + (x 1) ^ 2 := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial]
        ring
      rw [h]
      positivity
  have hC2 : MvPolynomial.C (2 : Rat) = (2 : MvPolynomial (Fin 2) Rat) := by
    rw [show (2 : Rat) = 1 + 1 by norm_num, MvPolynomial.C_add, MvPolynomial.C_1,
      one_add_one_eq_two]
  have hp : (MvPolynomial.X 0 ^ 2 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1
      + 2 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) Rat)
      = SOSCertificate.gramPoly ![MvPolynomial.X 0, MvPolynomial.X 1]
        !![(1 : Rat), -1; -1, 2] := by
    simp [SOSCertificate.gramPoly, Fin.sum_univ_two, hC2]
    ring
  rw [hp]
  exact SOSCertificate.eval_gramPoly_nonneg _ hQ _

/-- Test 2 (hypothesis is used): the non-PSD `Q = !![-1]` gives a negative value. -/
example : (SOSCertificate.gramPoly ![MvPolynomial.X 0] !![(-1 : Rat)]).eval₂
    (Rat.castHom Real) ![1] < (0 : Real) := by
  have hneg : (SOSCertificate.gramPoly ![MvPolynomial.X 0] !![(-1 : Rat)]).eval₂
      (Rat.castHom Real) ![1] = (-1 : Real) := by
    simp only [SOSCertificate.gramPoly, Fin.sum_univ_one,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Rat.coe_castHom,
      Matrix.cons_val_zero]
    norm_num
  rw [hneg]
  norm_num

/-- Test 2 (non-PSD check): `Q = !![-1]` is indeed not positive semidefinite. -/
example : ¬ (!![(-1 : Rat)] : Matrix (Fin 1) (Fin 1) Rat).PosSemidef := by
  intro h
  have hd : (0 : Rat) ≤ (-1 : Rat) := by
    have h0 := h.diag_nonneg (i := (0 : Fin 1))
    simpa using h0
  norm_num at hd

/-- Test 3 (boundary): the zero matrix gives the zero polynomial (evaluation `= 0`). -/
example (z : Fin 2 -> MvPolynomial (Fin 2) Rat) (x : Fin 2 -> Real) :
    (SOSCertificate.gramPoly z 0).eval₂ (Rat.castHom Real) x = 0 := by
  have h0 : SOSCertificate.gramPoly z 0 = 0 := by
    simp [SOSCertificate.gramPoly]
  rw [h0]
  exact MvPolynomial.eval₂_zero _ _

/-- Test 3 (boundary, empty index): the Gram polynomial over `Fin 0` is zero. -/
example (z : Fin 0 -> MvPolynomial (Fin 1) Rat) (Q : Matrix (Fin 0) (Fin 0) Rat) :
    SOSCertificate.gramPoly z Q = 0 := by
  simp [SOSCertificate.gramPoly]

/-- The monomial-vector corollary applies to the degree-`≤ 1` vector. -/
example (Q : Matrix (Option (Fin 2)) (Option (Fin 2)) Rat) (hQ : Q.PosSemidef)
    (x : Fin 2 -> Real) :
    0 ≤ (SOSCertificate.gramPoly (SOSCertificate.monomialVecDegLE1 2) Q).eval₂
      (Rat.castHom Real) x :=
  SOSCertificate.eval_gramPoly_monomials_nonneg 2 hQ x

-- Test 4 (axioms): the two main theorems depend only on the standard axioms.
#print axioms SOSCertificate.eval_gramPoly_nonneg
#print axioms SOSCertificate.posSemidef_map_ratCast
