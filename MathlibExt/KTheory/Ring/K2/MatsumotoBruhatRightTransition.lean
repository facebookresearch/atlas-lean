/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootTransport
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatFiber
public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalMonomialBridge
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootExtraction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

/-!
# Right-generator transitions of Bruhat factors

Over a field, extracts the coefficient of a right simple root from the upper
factor of a Bruhat decomposition and computes the monomial factor after
multiplication by an adjacent Weyl generator. The transition formulas
distinguish the cases determined by the coefficient and the permutation order.
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup
open PermutationBilinearCocycle

namespace MatsumotoBruhatRightTransition

section GeneralHelper

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

theorem toSLHom_elementary_eq_transvection
    {i j : ι} (hij : i < j) (a : R) :
    UpperElementary.toSLHom (UpperElementary.elementary i j hij a) =
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) a := by
  apply Subtype.ext
  rfl

theorem upperElementary_elementary_zero_eq_one
    {i j : ι} (hij : i ⋖ j) :
    UpperElementary.elementary i j hij.lt (0 : R) = 1 := by
  apply Subtype.ext
  simp [UpperElementary.coe_elementary]

omit [LinearOrder ι] in
theorem monomialSLHom_mul_transvection_eq
    (M : MonomialSL R ι) {i j : ι} (hij : i ≠ j) (a : R) :
    monomialSLHom R ι M *
        Matrix.SpecialLinearGroup.transvection hij a =
      Matrix.SpecialLinearGroup.transvection
          (fun h => hij (Equiv.injective M.1.right h))
          (((M.1.left (M.1.right i) : R) * a *
              ((M.1.left (M.1.right j))⁻¹ : Rˣ).val)) *
        monomialSLHom R ι M := by
  have hConj := monomialSLHom_conj_elementary (R := R) M i j hij a
  have h1 : (monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a *
      (monomialSLHom R ι M)⁻¹) * monomialSLHom R ι M =
      monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a := by
    calc (monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a *
        (monomialSLHom R ι M)⁻¹) * monomialSLHom R ι M
        = monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a *
            ((monomialSLHom R ι M)⁻¹ * monomialSLHom R ι M) := by
          simp only [mul_assoc]
      _ = monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a * 1 := by
          rw [inv_mul_cancel]
      _ = monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a := by
          rw [mul_one]
  calc monomialSLHom R ι M * Matrix.SpecialLinearGroup.transvection hij a
      = (monomialSLHom R ι M *
            Matrix.SpecialLinearGroup.transvection hij a *
            (monomialSLHom R ι M)⁻¹) *
          monomialSLHom R ι M := by
        exact h1.symm
    _ = Matrix.SpecialLinearGroup.transvection
            (fun h => hij (Equiv.injective M.1.right h))
            (((M.1.left (M.1.right i) : R) * a *
                ((M.1.left (M.1.right j))⁻¹ : Rˣ).val)) *
          monomialSLHom R ι M := by rw [hConj]

theorem transvection_upper_eq_toSLHom
    {i j : ι} (hij : i < j) (a : R) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) a =
      UpperElementary.toSLHom (UpperElementary.elementary i j hij a) := by
  rw [toSLHom_elementary_eq_transvection]

end GeneralHelper

section RightCoeff

variable (F : Type*) [Field F] (n : ℕ)

noncomputable def rightSimpleRootCoeff
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (_hij : i ⋖ j) : F :=
  (((Matrix.GeneralLinearGroup.bruhatRight (F := F) s :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)

noncomputable def rightResidual
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    upperElementarySubgroup (Fin n) F :=
  upperElementaryLeftResidual
    (Matrix.GeneralLinearGroup.bruhatRight s) hij

theorem rightResidual_zero
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    (((rightResidual F n s hij : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = 0) :=
  upperElementaryLeftResidual_zero
    (Matrix.GeneralLinearGroup.bruhatRight s) hij

theorem bruhatRight_eq_elementary_mul_residual
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.bruhatRight s =
      UpperElementary.elementary i j hij.lt
          (rightSimpleRootCoeff F n s hij) *
        rightResidual F n s hij := by
  unfold rightSimpleRootCoeff rightResidual
  exact upperElementary_leftExtraction
    (Matrix.GeneralLinearGroup.bruhatRight s) hij

theorem rightResidual_of_zero
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) (hZero : rightSimpleRootCoeff F n s hij = 0) :
    rightResidual F n s hij = Matrix.GeneralLinearGroup.bruhatRight s := by
  unfold rightResidual
  exact upperElementaryLeftResidual_of_zero _ hij hZero

theorem bruhatRight_coeff_unique
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) {a : F}
    {r : upperElementarySubgroup (Fin n) F}
    (hrZero : (((r : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = 0))
    (hEq : Matrix.GeneralLinearGroup.bruhatRight s =
        UpperElementary.elementary i j hij.lt a * r) :
    a = rightSimpleRootCoeff F n s hij := by
  unfold rightSimpleRootCoeff
  exact upperElementary_leftCoeff_unique
    (Matrix.GeneralLinearGroup.bruhatRight s) hij hrZero hEq

end RightCoeff

section FactorizationHelpers

variable {F : Type*} [Field F] {n : ℕ}
variable (s : Matrix.SpecialLinearGroup (Fin n) F)
variable {i j : Fin n} (hij : i ⋖ j)

theorem bruhat_factorization_rightExtract :
    s = UpperElementary.toSLHom
          (Matrix.GeneralLinearGroup.bruhatLeft s) *
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.bruhatMiddle s) *
        UpperElementary.toSLHom
          (UpperElementary.elementary i j hij.lt
              (rightSimpleRootCoeff F n s hij) *
            rightResidual F n s hij) := by
  have hS := Matrix.GeneralLinearGroup.bruhat_factorizationSL s
  have hR := bruhatRight_eq_elementary_mul_residual F n s hij
  calc s = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := hS
    _ = UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatLeft s) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (UpperElementary.elementary i j hij.lt
                (rightSimpleRootCoeff F n s hij) *
              rightResidual F n s hij) := by rw [hR]

end FactorizationHelpers

section ZeroBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_mul_weyl_right_zeroCoeff
    (hZero : rightSimpleRootCoeff F n s hij = 0) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.bruhatMiddle s *
        Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ) := by
  have hResZero : rightResidual F n s hij =
      Matrix.GeneralLinearGroup.bruhatRight s :=
    rightResidual_of_zero F n s hij hZero
  have hRZeroMat : (((rightResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    rightResidual_zero F n s hij
  have hEltZero : UpperElementary.elementary i j hij.lt
      (rightSimpleRootCoeff F n s hij) = 1 := by
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one hij
  have hFactor := bruhat_factorization_rightExtract s hij
  have hSLFactor :
      s = UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatLeft s) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom (rightResidual F n s hij) := by
    calc s = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s) *
              UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt
                    (rightSimpleRootCoeff F n s hij) *
                  rightResidual F n s hij) := hFactor
      _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            (UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt
                  (rightSimpleRootCoeff F n s hij)) *
              UpperElementary.toSLHom (rightResidual F n s hij)) := by
          rw [map_mul]
      _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom (rightResidual F n s hij) := by
          rw [hEltZero, map_one, one_mul]
  obtain ⟨t', ht'⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_right
      hij (-1 : Fˣ) hij.ne (rightResidual F n s hij) hRZeroMat
  have ht'Eq : UpperElementary.toSLHom (rightResidual F n s hij) *
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
        UpperElementary.toSLHom t' := ht'
  have hWeylMonomial :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne (-1 : Fˣ)
  have hMulWeyl : monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.bruhatMiddle s) *
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.bruhatMiddle s *
          Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ)) := by
    rw [hWeylMonomial, ← map_mul]
  have hFinalFactor :
      s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatLeft s) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s *
              Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
                (-1 : Fˣ)) *
          UpperElementary.toSLHom t' := by
    have h1 : s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        (UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom (rightResidual F n s hij)) *
          Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) :=
      congrArg (fun z => z * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
        (-1 : Fˣ)) hSLFactor
    calc s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)
        = (UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s) *
              UpperElementary.toSLHom (rightResidual F n s hij)) *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) := h1
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            (UpperElementary.toSLHom (rightResidual F n s hij) *
              Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
              UpperElementary.toSLHom t') := by rw [ht'Eq]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            (monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s) *
              Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) *
            UpperElementary.toSLHom t' := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s *
                Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
                  (-1 : Fˣ)) *
            UpperElementary.toSLHom t' := by rw [hMulWeyl]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))
    (Matrix.GeneralLinearGroup.bruhatLeft s)
    (Matrix.GeneralLinearGroup.bruhatMiddle s *
      Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ))
    t' hFinalFactor

end ZeroBranch

section PositiveBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_mul_weyl_right_posPerm
    (hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right i <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.bruhatMiddle s *
        Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ) := by
  let M := Matrix.GeneralLinearGroup.bruhatMiddle s
  have hResZero : (((rightResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    rightResidual_zero F n s hij
  have hFactor := bruhat_factorization_rightExtract s hij
  let c := rightSimpleRootCoeff F n s hij
  let E : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary i j hij.lt c
  let scaled : F :=
    ((M.1.left (M.1.right i) : F) * c *
      ((M.1.left (M.1.right j))⁻¹ : Fˣ).val)
  let E' : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary (M.1.right i) (M.1.right j) hPerm scaled
  have hConj : monomialSLHom F (Fin n) M *
      UpperElementary.toSLHom E =
      UpperElementary.toSLHom E' * monomialSLHom F (Fin n) M := by
    have hTrans : UpperElementary.toSLHom E =
        Matrix.SpecialLinearGroup.transvection hij.ne c := by
      apply toSLHom_elementary_eq_transvection
    have hTrans' : UpperElementary.toSLHom E' =
        Matrix.SpecialLinearGroup.transvection
          (ne_of_lt hPerm)
          scaled := by
      apply toSLHom_elementary_eq_transvection
    have hConjTrans := monomialSLHom_mul_transvection_eq (R := F) M hij.ne c
    calc monomialSLHom F (Fin n) M * UpperElementary.toSLHom E
        = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection hij.ne c := by
          rw [hTrans]
      _ = Matrix.SpecialLinearGroup.transvection
              (fun h => hij.ne (Equiv.injective M.1.right h))
              scaled * monomialSLHom F (Fin n) M := hConjTrans
      _ = UpperElementary.toSLHom E' * monomialSLHom F (Fin n) M := by
          rw [← hTrans']
  let newLeft : upperElementarySubgroup (Fin n) F :=
    Matrix.GeneralLinearGroup.bruhatLeft s * E'
  have hSNew :
      s = UpperElementary.toSLHom newLeft *
        monomialSLHom F (Fin n) M *
        UpperElementary.toSLHom (rightResidual F n s hij) := by
    have hMid : s = UpperElementary.toSLHom
                  (Matrix.GeneralLinearGroup.bruhatLeft s) *
                monomialSLHom F (Fin n) M *
                UpperElementary.toSLHom (E * rightResidual F n s hij) := by
      have : E = UpperElementary.elementary i j hij.lt
          (rightSimpleRootCoeff F n s hij) := rfl
      calc s = UpperElementary.toSLHom
                    (Matrix.GeneralLinearGroup.bruhatLeft s) *
                  monomialSLHom F (Fin n) M *
                  UpperElementary.toSLHom
                    (UpperElementary.elementary i j hij.lt
                      (rightSimpleRootCoeff F n s hij) *
                      rightResidual F n s hij) := hFactor
        _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom (E * rightResidual F n s hij) := rfl
    calc s = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom (E * rightResidual F n s hij) := hMid
      _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              monomialSLHom F (Fin n) M *
              (UpperElementary.toSLHom E *
                UpperElementary.toSLHom (rightResidual F n s hij)) := by
            rw [map_mul]
      _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              (monomialSLHom F (Fin n) M * UpperElementary.toSLHom E) *
              UpperElementary.toSLHom (rightResidual F n s hij) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              (UpperElementary.toSLHom E' * monomialSLHom F (Fin n) M) *
              UpperElementary.toSLHom (rightResidual F n s hij) := by
            rw [hConj]
      _ = (UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatLeft s) *
              UpperElementary.toSLHom E') *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom (rightResidual F n s hij) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom (rightResidual F n s hij) := by
            rw [map_mul]
  obtain ⟨t', ht'⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_right
      hij (-1 : Fˣ) hij.ne (rightResidual F n s hij) hResZero
  have ht'Eq : UpperElementary.toSLHom (rightResidual F n s hij) *
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
        UpperElementary.toSLHom t' := ht'
  have hWeylMonomial :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
            (-1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne
      (-1 : Fˣ)
  have hMulWeyl : monomialSLHom F (Fin n) M *
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      monomialSLHom F (Fin n)
        (M * Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
            (-1 : Fˣ)) := by
    rw [hWeylMonomial, ← map_mul]
  have hFinalFactor :
      s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            (M * Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
                (-1 : Fˣ)) *
          UpperElementary.toSLHom t' := by
    have h1 : s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        (UpperElementary.toSLHom newLeft *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom (rightResidual F n s hij)) *
          Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) :=
      congrArg (fun z => z * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
        (-1 : Fˣ)) hSNew
    calc s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)
        = (UpperElementary.toSLHom newLeft *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom (rightResidual F n s hij)) *
          Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) := h1
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom (rightResidual F n s hij) *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
            UpperElementary.toSLHom t') := by rw [ht'Eq]
      _ = UpperElementary.toSLHom newLeft *
          (monomialSLHom F (Fin n) M *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) *
          UpperElementary.toSLHom t' := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            (M * Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
                (-1 : Fˣ)) *
          UpperElementary.toSLHom t' := by rw [hMulWeyl]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))
    newLeft
    (M * Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (-1 : Fˣ))
    t' hFinalFactor

end PositiveBranch

section NegativeBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_mul_weyl_right_negPerm
    (v : Fˣ) (hv : rightSimpleRootCoeff F n s hij = (v : F))
    (hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right j <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right i) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.bruhatMiddle s *
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v := by
  let M := Matrix.GeneralLinearGroup.bruhatMiddle s
  have hResZero : (((rightResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    rightResidual_zero F n s hij
  have hFactor := bruhat_factorization_rightExtract s hij
  have hEeq : UpperElementary.elementary i j hij.lt
      (rightSimpleRootCoeff F n s hij) =
      UpperElementary.elementary i j hij.lt (v : F) := by
    rw [hv]
  have hRankOne : Matrix.SpecialLinearGroup.transvection hij.ne (v : F) *
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      Matrix.SpecialLinearGroup.transvection hij.ne.symm (↑v⁻¹ : F) *
        Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v *
        Matrix.SpecialLinearGroup.transvection hij.ne (-(↑v⁻¹ : F)) :=
    Matrix.GeneralLinearGroup.rankOneSL_right i j hij.ne v
  have hTransE : UpperElementary.toSLHom
      (UpperElementary.elementary i j hij.lt (v : F)) =
      Matrix.SpecialLinearGroup.transvection hij.ne (v : F) := by
    apply toSLHom_elementary_eq_transvection
  obtain ⟨tRes, htRes⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_right
      hij (-1 : Fˣ) hij.ne (rightResidual F n s hij) hResZero
  have htResEq : UpperElementary.toSLHom (rightResidual F n s hij) *
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
        UpperElementary.toSLHom tRes := htRes
  let lowerCoeff : F := (↑v⁻¹ : F)
  let lowerScaled : F :=
    ((M.1.left (M.1.right j) : F) * lowerCoeff *
      ((M.1.left (M.1.right i))⁻¹ : Fˣ).val)
  let lowerConj : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary (M.1.right j) (M.1.right i) hPerm lowerScaled
  have hLowerConj : monomialSLHom F (Fin n) M *
      Matrix.SpecialLinearGroup.transvection hij.ne.symm (↑v⁻¹ : F) =
      UpperElementary.toSLHom lowerConj *
        monomialSLHom F (Fin n) M := by
    have hConj := monomialSLHom_mul_transvection_eq (R := F) M hij.ne.symm
      (↑v⁻¹ : F)
    have hToSL : UpperElementary.toSLHom lowerConj =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hPerm) lowerScaled := by
      apply toSLHom_elementary_eq_transvection
    have hEq : Matrix.SpecialLinearGroup.transvection
          (fun h => hij.ne.symm (Equiv.injective M.1.right h))
          (((M.1.left (M.1.right j) : F) * (↑v⁻¹ : F) *
              ((M.1.left (M.1.right i))⁻¹ : Fˣ).val)) =
        UpperElementary.toSLHom lowerConj := by
      rw [← hToSL]
    calc monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection hij.ne.symm (↑v⁻¹ : F)
        = Matrix.SpecialLinearGroup.transvection
              (fun h => hij.ne.symm (Equiv.injective M.1.right h))
              (((M.1.left (M.1.right j) : F) * (↑v⁻¹ : F) *
                  ((M.1.left (M.1.right i))⁻¹ : Fˣ).val)) *
            monomialSLHom F (Fin n) M := hConj
      _ = UpperElementary.toSLHom lowerConj *
            monomialSLHom F (Fin n) M := by rw [← hEq]
  let newLeft : upperElementarySubgroup (Fin n) F :=
    Matrix.GeneralLinearGroup.bruhatLeft s * lowerConj
  let upperNeg : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary i j hij.lt (-(↑v⁻¹ : F))
  let newRight : upperElementarySubgroup (Fin n) F :=
    upperNeg * tRes
  have hTorusMonomial :
      Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v =
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v) :=
    Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom i j hij.ne v
  have hM_Torus : monomialSLHom F (Fin n) M *
      Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v =
      monomialSLHom F (Fin n)
        (M * Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v) := by
    rw [hTorusMonomial, ← map_mul]
  have hS_decomp :
      s = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt (v : F) *
                rightResidual F n s hij) := by
    calc s = UpperElementary.toSLHom
                  (Matrix.GeneralLinearGroup.bruhatLeft s) *
                monomialSLHom F (Fin n) M *
                UpperElementary.toSLHom
                  (UpperElementary.elementary i j hij.lt
                      (rightSimpleRootCoeff F n s hij) *
                    rightResidual F n s hij) := hFactor
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt (v : F) *
                rightResidual F n s hij) := by
          rw [hEeq]
  have hFinal :
      s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            (M * Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v) *
          UpperElementary.toSLHom newRight := by
    have h1 : s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) =
        (UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt (v : F) *
                rightResidual F n s hij)) *
          Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) :=
      congrArg (fun z => z * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
        (-1 : Fˣ)) hS_decomp
    have hNeg : Matrix.SpecialLinearGroup.transvection hij.ne
        (-(↑v⁻¹ : F)) =
        UpperElementary.toSLHom upperNeg := by
      symm
      apply toSLHom_elementary_eq_transvection
    calc s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)
        = (UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            (UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt (v : F)) *
              UpperElementary.toSLHom (rightResidual F n s hij))) *
          Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) := by
          rw [h1, map_mul]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            (Matrix.SpecialLinearGroup.transvection hij.ne (v : F) *
              (UpperElementary.toSLHom (rightResidual F n s hij) *
                Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))) := by
          rw [hTransE]
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            (Matrix.SpecialLinearGroup.transvection hij.ne (v : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
                UpperElementary.toSLHom tRes)) := by
          rw [htResEq]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            (Matrix.SpecialLinearGroup.transvection hij.ne (v : F) *
              Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) *
              UpperElementary.toSLHom tRes) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n) M *
            (Matrix.SpecialLinearGroup.transvection hij.ne.symm (↑v⁻¹ : F) *
              Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v *
              Matrix.SpecialLinearGroup.transvection hij.ne (-(↑v⁻¹ : F)) *
              UpperElementary.toSLHom tRes) := by
          rw [hRankOne]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            (monomialSLHom F (Fin n) M *
              Matrix.SpecialLinearGroup.transvection hij.ne.symm (↑v⁻¹ : F)) *
            Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v *
            (Matrix.SpecialLinearGroup.transvection hij.ne (-(↑v⁻¹ : F)) *
              UpperElementary.toSLHom tRes) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            (UpperElementary.toSLHom lowerConj *
              monomialSLHom F (Fin n) M) *
            Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v *
            (UpperElementary.toSLHom upperNeg *
              UpperElementary.toSLHom tRes) := by
          rw [hLowerConj, hNeg]
      _ = (UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            UpperElementary.toSLHom lowerConj) *
          monomialSLHom F (Fin n) M *
          Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v *
          UpperElementary.toSLHom newRight := by
          rw [show UpperElementary.toSLHom upperNeg * UpperElementary.toSLHom tRes =
              UpperElementary.toSLHom newRight from by
                simp [newRight, map_mul]]
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          (monomialSLHom F (Fin n) M *
            Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v) *
          UpperElementary.toSLHom newRight := by
          rw [show UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
              UpperElementary.toSLHom lowerConj =
              UpperElementary.toSLHom newLeft from by
                simp [newLeft, map_mul]]
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            (M * Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v) *
          UpperElementary.toSLHom newRight := by rw [hM_Torus]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))
    newLeft
    (M * Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)
    newRight hFinal

end NegativeBranch

section Exhaustive

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

noncomputable def torusUnitOfCoeff
    (c : F) (hc : c ≠ 0) : Fˣ :=
  Units.mk0 c hc

theorem torusUnitOfCoeff_val (c : F) (hc : c ≠ 0) :
    (torusUnitOfCoeff c hc : F) = c := by
  simp [torusUnitOfCoeff]

theorem torusUnitOfCoeff_unique (c : F) (hc : c ≠ 0) (v : Fˣ)
    (hv : (v : F) = c) :
    v = torusUnitOfCoeff c hc := by
  apply Units.ext
  simp [torusUnitOfCoeff, hv]

theorem bruhatRightTransition_cases :
    (rightSimpleRootCoeff F n s hij = 0 ∧
      Matrix.GeneralLinearGroup.bruhatMiddle
          (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
              (-1 : Fˣ)) =
        Matrix.GeneralLinearGroup.bruhatMiddle s *
          Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
            (-1 : Fˣ)) ∨
    ((Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right i <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j ∧
      Matrix.GeneralLinearGroup.bruhatMiddle
          (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
              (-1 : Fˣ)) =
        Matrix.GeneralLinearGroup.bruhatMiddle s *
          Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
            (-1 : Fˣ)) ∨
    (∃ v : Fˣ, rightSimpleRootCoeff F n s hij = (v : F) ∧
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right i ∧
        Matrix.GeneralLinearGroup.bruhatMiddle
            (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                (-1 : Fˣ)) =
          Matrix.GeneralLinearGroup.bruhatMiddle s *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v) := by
  by_cases hZero : rightSimpleRootCoeff F n s hij = 0
  · exact Or.inl ⟨hZero, bruhatMiddle_mul_weyl_right_zeroCoeff hij s hZero⟩
  · by_cases hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right i <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j
    · exact Or.inr (Or.inl ⟨hPerm,
        bruhatMiddle_mul_weyl_right_posPerm hij s hPerm⟩)
    · have hNotPos : ¬ (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right i <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j := hPerm
      have hNe : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right i ≠
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right j := by
        intro heq
        have hinj := Equiv.injective
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right
        have hijNe : i ≠ j := hij.ne
        exact hijNe (hinj heq)
      have hNeg : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right j <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right i := by
        have hTotal := lt_or_gt_of_ne hNe
        rcases hTotal with hLt | hGt
        · exact absurd hLt hNotPos
        · exact hGt
      have hcNe : rightSimpleRootCoeff F n s hij ≠ 0 := hZero
      let v := torusUnitOfCoeff (rightSimpleRootCoeff F n s hij) hcNe
      have hv : rightSimpleRootCoeff F n s hij = (v : F) :=
        (torusUnitOfCoeff_val _ hcNe).symm
      refine Or.inr (Or.inr ⟨v, hv, hNeg, ?_⟩)
      exact bruhatMiddle_mul_weyl_right_negPerm hij s v hv hNeg

end Exhaustive

end MatsumotoBruhatRightTransition
