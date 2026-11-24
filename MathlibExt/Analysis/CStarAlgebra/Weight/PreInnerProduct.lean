/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.FiniteValueRelations
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The actual weight polarization on its original finite-square domain

Finite-positive signed relations prove the Hermitian, additive and scalar
laws of the literal global-weight polarization. Its diagonal is exactly
the original finite square value. These proofs construct the actual
pre-inner-product core, with no supplied scalar extension or inner certificate.

A type copy of the original finite-square module prevents its ambient
operator norm from being confused with the weight-induced norm. The
pre-inner-product Core below is constructed from the proved scalar kernel.
The induced norm, faithfulness, normality, completion representation and Tomita data
remain separate obligations; no original source theorem is selected as DATA.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The original square difference is the symmetric sum of its two cross terms. -/
theorem leftSquare_difference (x y : A) :
    (leftSquare (x + y) : A) - (leftSquare (x - y) : A) =
      (star x * y + star y * x) + (star x * y + star y * x) := by
  simp only [leftSquare, star_add, star_sub, add_mul, mul_add, sub_mul, mul_sub]
  abel

/-- The finite-square value at zero is the original weight value at zero. -/
theorem Weight.finiteSquareValue_zero (φ : Weight A) : φ.finiteSquareValue 0 = 0 := by
  have hzero : leftSquare (0 : A) = positiveZero A := by
    apply Subtype.ext
    simp only [leftSquare, positiveZero, star_zero, zero_mul]
  change (φ.value (leftSquare (0 : A))).toReal = 0
  rw [hzero, φ.zero_value, ENNReal.toReal_zero]

/-- Every finite-square value is a genuinely nonnegative real number. -/
theorem Weight.finiteSquareValue_nonneg (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    0 ≤ φ.finiteSquareValue x :=
  ENNReal.toReal_nonneg

/-- Taking the original negative does not change the original positive square value. -/
theorem Weight.finiteSquareValue_neg (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquareValue (-x) = φ.finiteSquareValue x := by
  have hneg : leftSquare (-(x : A)) = leftSquare (x : A) := by
    apply Subtype.ext
    simp only [leftSquare, star_neg, neg_mul, mul_neg, neg_neg]
  change (φ.value (leftSquare (-(x : A)))).toReal = (φ.value (leftSquare (x : A))).toReal
  rw [hneg]

/-- Original complex scaling changes the finite square by exactly its scalar norm square. -/
theorem Weight.finiteSquareValue_smul (φ : Weight A) (c : ℂ) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquareValue (c • x) = ‖c‖ ^ 2 * φ.finiteSquareValue x := by
  have hsquare : leftSquare (c • (x : A)) =
      positiveSmul (NNReal.mk (‖c‖ ^ 2) (sq_nonneg ‖c‖)) (leftSquare (x : A)) :=
    leftSquare_smul c (x : A)
  have hvalue := congrArg (fun z : PositiveElement A => (φ.value z).toReal) hsquare
  change (φ.value (leftSquare (c • (x : A)))).toReal =
    ‖c‖ ^ 2 * (φ.value (leftSquare (x : A))).toReal
  exact hvalue.trans (φ.toReal_positiveSmul (NNReal.mk (‖c‖ ^ 2) (sq_nonneg ‖c‖)) (leftSquare (x : A)))

/-- Real polarization of the original finite square is zero at the zero first argument. -/
theorem Weight.finiteSquarePolarRe_zero (φ : Weight A) (y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe 0 y = 0 := by
  simp only [Weight.finiteSquarePolarRe, zero_add, zero_sub, φ.finiteSquareValue_neg,
    sub_self, zero_div]

/-- Original finite-positive difference addition proves additivity of the real pairing. -/
theorem Weight.finiteSquarePolarRe_add (φ : Weight A) (x y z : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (x + y) z = φ.finiteSquarePolarRe x z + φ.finiteSquarePolarRe y z := by
  have hraw :
      (leftSquare (((x + y) + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((x + y) - z : φ.finiteSquareSubmodule) : A) : A) =
      ((leftSquare ((x + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - z : φ.finiteSquareSubmodule) : A) : A)) +
      ((leftSquare ((y + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((y - z : φ.finiteSquareSubmodule) : A) : A)) := by
    change (leftSquare ((x : A) + (y : A) + (z : A)) : A) -
      (leftSquare ((x : A) + (y : A) - (z : A)) : A) =
      ((leftSquare ((x : A) + (z : A)) : A) - (leftSquare ((x : A) - (z : A)) : A)) +
      ((leftSquare ((y : A) + (z : A)) : A) - (leftSquare ((y : A) - (z : A)) : A))
    simp only [leftSquare_difference, star_add, add_mul, mul_add]
    abel
  have h := φ.finite_toReal_sub_eq_add_sub
    (leftSquare (((x + y) + z : φ.finiteSquareSubmodule) : A))
    (leftSquare (((x + y) - z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y + z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y - z : φ.finiteSquareSubmodule) : A))
    (x + y + z).property (x + y - z).property (x + z).property (x - z).property
    (y + z).property (y - z).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- Negating the original first argument negates the actual real pairing. -/
theorem Weight.finiteSquarePolarRe_neg (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (-x) y = -φ.finiteSquarePolarRe x y := by
  have h := φ.finiteSquarePolarRe_add x (-x) y
  rw [add_neg_cancel, φ.finiteSquarePolarRe_zero] at h
  linarith

/-- The actual real pairing is symmetric by the original star-product difference identity. -/
theorem Weight.finiteSquarePolarRe_symm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe x y = φ.finiteSquarePolarRe y x := by
  have hraw :
      (leftSquare ((x + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare ((y + x : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((y - x : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare ((x : A) + (y : A)) : A) - (leftSquare ((x : A) - (y : A)) : A) =
      (leftSquare ((y : A) + (x : A)) : A) - (leftSquare ((y : A) - (x : A)) : A)
    simp only [leftSquare_difference]
    abel
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare ((x + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y + x : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y - x : φ.finiteSquareSubmodule) : A))
    (x + y).property (x - y).property (y + x).property (y - x).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- Original real scalar multiplication scales the actual real pairing. -/
theorem Weight.finiteSquarePolarRe_smul_real (φ : Weight A) (r : ℝ)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe ((RCLike.ofReal r : ℂ) • x) y = r * φ.finiteSquarePolarRe x y := by
  have hscalar : (RCLike.ofReal r : ℂ) • (x : A) = r • (x : A) :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r (x : A)).symm
  have hraw :
      (leftSquare ((((RCLike.ofReal r : ℂ) • x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((((RCLike.ofReal r : ℂ) • x) - y : φ.finiteSquareSubmodule) : A) : A) =
      r • ((leftSquare ((x + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - y : φ.finiteSquareSubmodule) : A) : A)) := by
    change (leftSquare ((RCLike.ofReal r : ℂ) • (x : A) + (y : A)) : A) -
      (leftSquare ((RCLike.ofReal r : ℂ) • (x : A) - (y : A)) : A) =
      r • ((leftSquare ((x : A) + (y : A)) : A) - (leftSquare ((x : A) - (y : A)) : A))
    rw [hscalar]
    simp only [leftSquare_difference, star_smul, star_trivial, smul_mul_assoc,
      mul_smul_comm, smul_add]
  have h := φ.finite_toReal_sub_eq_real_smul_sub r
    (leftSquare ((((RCLike.ofReal r : ℂ) • x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((((RCLike.ofReal r : ℂ) • x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - y : φ.finiteSquareSubmodule) : A))
    (((RCLike.ofReal r : ℂ) • x) + y).property (((RCLike.ofReal r : ℂ) • x) - y).property
    (x + y).property (x - y).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- The original imaginary cross difference changes sign when the arguments are exchanged. -/
theorem Weight.finiteSquarePolarRe_I_antisymm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (Complex.I • x) y = -φ.finiteSquarePolarRe (Complex.I • y) x := by
  have hraw :
      (leftSquare (((Complex.I • x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((Complex.I • x) - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare (((Complex.I • y) - x : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((Complex.I • y) + x : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare (Complex.I • (x : A) + (y : A)) : A) -
      (leftSquare (Complex.I • (x : A) - (y : A)) : A) =
      (leftSquare (Complex.I • (y : A) - (x : A)) : A) -
      (leftSquare (Complex.I • (y : A) + (x : A)) : A)
    have hreverse :
        (leftSquare (Complex.I • (y : A) - (x : A)) : A) -
          (leftSquare (Complex.I • (y : A) + (x : A)) : A) =
        -((leftSquare (Complex.I • (y : A) + (x : A)) : A) -
          (leftSquare (Complex.I • (y : A) - (x : A)) : A)) := by abel
    rw [hreverse]
    simp only [leftSquare_difference, star_smul, Complex.star_def, Complex.conj_I,
      neg_smul, neg_mul, smul_mul_assoc, mul_smul_comm]
    abel
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare (((Complex.I • x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • y) - x : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • y) + x : φ.finiteSquareSubmodule) : A))
    ((Complex.I • x) + y).property ((Complex.I • x) - y).property
    ((Complex.I • y) - x).property ((Complex.I • y) + x).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- The actual complex polarization is Hermitian. -/
theorem Weight.finiteSquarePolarInner_conj_symm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    (starRingEnd ℂ) (φ.finiteSquarePolarInner y x) = φ.finiteSquarePolarInner x y := by
  apply Complex.ext
  · rw [Complex.conj_re]
    change φ.finiteSquarePolarRe y x = φ.finiteSquarePolarRe x y
    exact φ.finiteSquarePolarRe_symm y x
  · rw [Complex.conj_im]
    change -φ.finiteSquarePolarRe (Complex.I • y) x = φ.finiteSquarePolarRe (Complex.I • x) y
    have h := φ.finiteSquarePolarRe_I_antisymm y x
    linarith

/-- The actual complex polarization is additive in the original first argument. -/
theorem Weight.finiteSquarePolarInner_add (φ : Weight A) (x y z : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (x + y) z = φ.finiteSquarePolarInner x z + φ.finiteSquarePolarInner y z := by
  apply Complex.ext
  · rw [Complex.add_re]
    change φ.finiteSquarePolarRe (x + y) z = φ.finiteSquarePolarRe x z + φ.finiteSquarePolarRe y z
    exact φ.finiteSquarePolarRe_add x y z
  · rw [Complex.add_im]
    change φ.finiteSquarePolarRe (Complex.I • (x + y)) z =
      φ.finiteSquarePolarRe (Complex.I • x) z + φ.finiteSquarePolarRe (Complex.I • y) z
    rw [smul_add]
    exact φ.finiteSquarePolarRe_add (Complex.I • x) (Complex.I • y) z

/-- Real scalars act on the actual complex pairing by their original real embedding. -/
theorem Weight.finiteSquarePolarInner_smul_real (φ : Weight A) (r : ℝ)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner ((RCLike.ofReal r : ℂ) • x) y =
      (RCLike.ofReal r : ℂ) * φ.finiteSquarePolarInner x y := by
  have hcomm : Complex.I • ((RCLike.ofReal r : ℂ) • x) =
      (RCLike.ofReal r : ℂ) • (Complex.I • x) := smul_comm Complex.I (RCLike.ofReal r : ℂ) x
  have hre : (RCLike.ofReal r : ℂ).re = r := by
    simpa only [RCLike.re_to_complex] using (RCLike.ofReal_re (K := ℂ) r)
  have him : (RCLike.ofReal r : ℂ).im = 0 := by
    simpa only [RCLike.im_to_complex] using (RCLike.ofReal_im (K := ℂ) r)
  apply Complex.ext
  · rw [Complex.mul_re, hre, him]
    change φ.finiteSquarePolarRe ((RCLike.ofReal r : ℂ) • x) y =
      r * φ.finiteSquarePolarRe x y - 0 * φ.finiteSquarePolarRe (Complex.I • x) y
    rw [zero_mul, sub_zero]
    exact φ.finiteSquarePolarRe_smul_real r x y
  · rw [Complex.mul_im, hre, him]
    change φ.finiteSquarePolarRe (Complex.I • ((RCLike.ofReal r : ℂ) • x)) y =
      r * φ.finiteSquarePolarRe (Complex.I • x) y + 0 * φ.finiteSquarePolarRe x y
    rw [hcomm, zero_mul, add_zero]
    exact φ.finiteSquarePolarRe_smul_real r (Complex.I • x) y

/-- Multiplication of the first argument by i gives the original conjugate-linear sign. -/
theorem Weight.finiteSquarePolarInner_smul_I (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (Complex.I • x) y = -Complex.I * φ.finiteSquarePolarInner x y := by
  have hII : Complex.I • (Complex.I • x) = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  apply Complex.ext
  · rw [Complex.mul_re]
    change φ.finiteSquarePolarRe (Complex.I • x) y =
      (-Complex.I).re * φ.finiteSquarePolarRe x y -
        (-Complex.I).im * φ.finiteSquarePolarRe (Complex.I • x) y
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  · rw [Complex.mul_im]
    change φ.finiteSquarePolarRe (Complex.I • (Complex.I • x)) y =
      (-Complex.I).re * φ.finiteSquarePolarRe (Complex.I • x) y +
        (-Complex.I).im * φ.finiteSquarePolarRe x y
    rw [hII, φ.finiteSquarePolarRe_neg]
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring

/-- Every original complex scalar acts conjugate linearly in the first argument. -/
theorem Weight.finiteSquarePolarInner_smul (φ : Weight A) (c : ℂ) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (c • x) y = (starRingEnd ℂ) c * φ.finiteSquarePolarInner x y := by
  let r : ℝ := RCLike.re c
  let s : ℝ := RCLike.im c
  have hc : c = (RCLike.ofReal r : ℂ) + (RCLike.ofReal s : ℂ) * Complex.I :=
    (RCLike.re_add_im c).symm
  rw [hc, add_smul, φ.finiteSquarePolarInner_add,
    ← smul_smul (RCLike.ofReal s : ℂ) Complex.I x,
    φ.finiteSquarePolarInner_smul_real r, φ.finiteSquarePolarInner_smul_real s,
    φ.finiteSquarePolarInner_smul_I]
  simp only [map_add, map_mul, RCLike.conj_ofReal, Complex.conj_I]
  ring

/-- The real diagonal is exactly the original finite square weight value. -/
theorem Weight.finiteSquarePolarRe_self (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe x x = φ.finiteSquareValue x := by
  have htwo : x + x = (2 : ℂ) • x := (two_smul ℂ x).symm
  simp only [Weight.finiteSquarePolarRe, htwo, sub_self, φ.finiteSquareValue_zero,
    φ.finiteSquareValue_smul]
  norm_num

/-- The actual complex diagonal is the original positive scalar weight value. -/
theorem Weight.finiteSquarePolarInner_self (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner x x = (RCLike.ofReal (φ.finiteSquareValue x) : ℂ) := by
  have him := φ.finiteSquarePolarRe_I_antisymm x x
  have hre : (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).re = φ.finiteSquareValue x := by
    simpa only [RCLike.re_to_complex] using (RCLike.ofReal_re (K := ℂ) (φ.finiteSquareValue x))
  have himzero : (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).im = 0 := by
    simpa only [RCLike.im_to_complex] using (RCLike.ofReal_im (K := ℂ) (φ.finiteSquareValue x))
  apply Complex.ext
  · change φ.finiteSquarePolarRe x x = (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).re
    rw [φ.finiteSquarePolarRe_self, hre]
  · change φ.finiteSquarePolarRe (Complex.I • x) x =
      (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).im
    rw [himzero]
    linarith

/-- A type copy of the exact original linear domain for the induced weight norm. -/
def Weight.PreGNS (φ : Weight A) : Type u := φ.finiteSquareSubmodule

/-- The pre-GNS copy has exactly the original finite-square additive group. -/
instance Weight.preGNSAddCommGroup (φ : Weight A) : AddCommGroup φ.PreGNS :=
  inferInstanceAs (AddCommGroup φ.finiteSquareSubmodule)

/-- The pre-GNS copy has exactly the original complex scalar action. -/
instance Weight.preGNSModule (φ : Weight A) : Module ℂ φ.PreGNS :=
  inferInstanceAs (Module ℂ φ.finiteSquareSubmodule)

/-- The pre-GNS copy forgets to exactly the original finite-square module. -/
def Weight.preGNSLinearEquiv (φ : Weight A) : φ.PreGNS ≃ₗ[ℂ] φ.finiteSquareSubmodule where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual pre-inner-product fields are proved from the original scalar weight values. -/
@[instance_reducible]
def Weight.preGNSPreInnerProduct (φ : Weight A) : PreInnerProductSpace.Core ℂ φ.PreGNS where
  inner x y := φ.finiteSquarePolarInner (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y)
  conj_inner_symm x y := φ.finiteSquarePolarInner_conj_symm _ _
  re_inner_nonneg x := by
    rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re]
    exact φ.finiteSquareValue_nonneg _
  add_left x y z := by
    rw [map_add]
    exact φ.finiteSquarePolarInner_add _ _ _
  smul_left x y c := by
    change φ.finiteSquarePolarInner (φ.preGNSLinearEquiv (c • x)) (φ.preGNSLinearEquiv y) = _
    rw [map_smul]
    exact φ.finiteSquarePolarInner_smul _ _ _

end

end CStarAlgebra.ScalarWeight
