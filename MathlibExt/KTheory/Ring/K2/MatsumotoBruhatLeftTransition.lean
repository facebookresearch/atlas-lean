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

public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatRightTransition
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootTransport
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootExtraction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootFactorUniqueness

/-!
# Left simple-root transitions in Bruhat decompositions

This module computes the left Bruhat factors under multiplication by simple-root
transvections. It tracks the residual upper-elementary factor, Weyl and torus
factors, and the field coefficients needed for the Matsumoto extension.
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup
open PermutationBilinearCocycle

namespace MatsumotoBruhatLeftTransition

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
theorem transvection_mul_monomialSLHom_eq
    (M : MonomialSL R ι) {i j : ι} (hij : i ≠ j) (a : R) :
    Matrix.SpecialLinearGroup.transvection hij a *
        monomialSLHom R ι M =
      monomialSLHom R ι M *
        Matrix.SpecialLinearGroup.transvection
          (fun h => hij (Equiv.injective (Equiv.symm M.1.right) h))
          ((((M.1.left i)⁻¹ : Rˣ).val * a * (M.1.left j : R))) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  let hij' : (Equiv.symm M.1.right i) ≠ (Equiv.symm M.1.right j) :=
    fun h => hij (Equiv.injective (Equiv.symm M.1.right) h)
  let scaled : R := (((M.1.left i)⁻¹ : Rˣ).val * a * (M.1.left j : R))
  have hGL :=
    elementary_mul_monomialMatrixHom (R := R)
      (M : MonomialBase Rˣ ι) i j hij a
  have hToGLLeft :
      Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij a *
            monomialSLHom R ι M) =
        (Matrix.GeneralLinearGroup.elementary i j hij a : GL ι R) *
          monomialMatrixHom R ι (M : MonomialBase Rˣ ι) := by
    calc Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection hij a *
              monomialSLHom R ι M)
        = Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij a) *
            Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι M) := by
          simp [map_mul]
      _ = (Matrix.GeneralLinearGroup.elementary i j hij a : GL ι R) *
            monomialMatrixHom R ι (M : MonomialBase Rˣ ι) := by
          have h1 :
              Matrix.SpecialLinearGroup.toGL
                  (Matrix.SpecialLinearGroup.transvection hij a) =
                (Matrix.GeneralLinearGroup.elementary i j hij a : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe]
          have h2 :
              Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι M) =
                monomialMatrixHom R ι (M : MonomialBase Rˣ ι) := by
            rw [monomialSLHom_toGL]
          rw [h1, h2]
  have hToGLRight :
      Matrix.SpecialLinearGroup.toGL
          (monomialSLHom R ι M *
            Matrix.SpecialLinearGroup.transvection hij' scaled) =
        monomialMatrixHom R ι (M : MonomialBase Rˣ ι) *
          (Matrix.GeneralLinearGroup.elementary
            (Equiv.symm M.1.right i) (Equiv.symm M.1.right j) hij' scaled
            : GL ι R) := by
    calc Matrix.SpecialLinearGroup.toGL
            (monomialSLHom R ι M *
              Matrix.SpecialLinearGroup.transvection hij' scaled)
        = Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι M) *
            Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij' scaled) := by
          simp [map_mul]
      _ = monomialMatrixHom R ι (M : MonomialBase Rˣ ι) *
            (Matrix.GeneralLinearGroup.elementary
              (Equiv.symm M.1.right i) (Equiv.symm M.1.right j) hij' scaled
              : GL ι R) := by
          have h1 :
              Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι M) =
                monomialMatrixHom R ι (M : MonomialBase Rˣ ι) := by
            rw [monomialSLHom_toGL]
          have h2 :
              Matrix.SpecialLinearGroup.toGL
                  (Matrix.SpecialLinearGroup.transvection hij' scaled) =
                (Matrix.GeneralLinearGroup.elementary
                  (Equiv.symm M.1.right i) (Equiv.symm M.1.right j) hij' scaled
                  : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe]
          rw [h1, h2]
  calc Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij a *
            monomialSLHom R ι M)
      = (Matrix.GeneralLinearGroup.elementary i j hij a : GL ι R) *
          monomialMatrixHom R ι (M : MonomialBase Rˣ ι) := hToGLLeft
    _ = monomialMatrixHom R ι (M : MonomialBase Rˣ ι) *
          (Matrix.GeneralLinearGroup.elementary
            (Equiv.symm M.1.right i) (Equiv.symm M.1.right j) hij' scaled
            : GL ι R) := hGL
    _ = Matrix.SpecialLinearGroup.toGL
            (monomialSLHom R ι M *
              Matrix.SpecialLinearGroup.transvection hij' scaled) :=
        hToGLRight.symm

theorem transvection_upper_eq_toSLHom
    {i j : ι} (hij : i < j) (a : R) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) a =
      UpperElementary.toSLHom (UpperElementary.elementary i j hij a) := by
  rw [toSLHom_elementary_eq_transvection]

omit [LinearOrder ι] in
theorem weylSLUnit_one_mul_transvection_neg
    {i j : ι} (hij : i ≠ j) (v : Rˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij (1 : Rˣ) *
        Matrix.SpecialLinearGroup.transvection hij (-(v : R)) =
      Matrix.SpecialLinearGroup.transvection hij ((↑v⁻¹ : R)) *
        (Matrix.GeneralLinearGroup.torusSLUnit i j hij v)⁻¹ *
        Matrix.SpecialLinearGroup.transvection hij.symm (-(↑v⁻¹ : R)) := by
  have hRank := Matrix.GeneralLinearGroup.rankOneSL_right
    (R := R) i j hij v
  calc Matrix.GeneralLinearGroup.weylSLUnit i j hij (1 : Rˣ) *
          Matrix.SpecialLinearGroup.transvection hij (-(v : R))
      = (Matrix.GeneralLinearGroup.weylSLUnit i j hij (-1 : Rˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection hij (v : R))⁻¹ := by
        rw [Matrix.GeneralLinearGroup.weylSLUnit_inv (R := R) i j hij (-1 : Rˣ)]
        simp [Matrix.SpecialLinearGroup.transvection_inv]
      _ = (Matrix.SpecialLinearGroup.transvection hij (v : R) *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij (-1 : Rˣ))⁻¹ := by
        rw [_root_.mul_inv_rev]
      _ = (Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R) *
            Matrix.GeneralLinearGroup.torusSLUnit i j hij v *
            Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R)))⁻¹ := by
        rw [hRank]
      _ = (Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R)))⁻¹ *
            (Matrix.GeneralLinearGroup.torusSLUnit i j hij v)⁻¹ *
            (Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R))⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      _ = Matrix.SpecialLinearGroup.transvection hij (↑v⁻¹ : R) *
            (Matrix.GeneralLinearGroup.torusSLUnit i j hij v)⁻¹ *
            Matrix.SpecialLinearGroup.transvection hij.symm (-(↑v⁻¹ : R)) := by
        simp [Matrix.SpecialLinearGroup.transvection_inv]

end GeneralHelper

section LeftCoeff

variable (F : Type*) [Field F] (n : ℕ)

noncomputable def leftSimpleRootCoeff
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (_hij : i ⋖ j) : F :=
  (((Matrix.GeneralLinearGroup.bruhatLeft (F := F) s :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)

noncomputable def leftResidual
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    upperElementarySubgroup (Fin n) F :=
  upperElementaryRightResidual
    (Matrix.GeneralLinearGroup.bruhatLeft s) hij

theorem leftResidual_zero
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    (((leftResidual F n s hij : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = 0) :=
  upperElementaryRightResidual_zero
    (Matrix.GeneralLinearGroup.bruhatLeft s) hij

theorem bruhatLeft_eq_residual_mul_elementary
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.bruhatLeft s =
      leftResidual F n s hij *
        UpperElementary.elementary i j hij.lt
          (leftSimpleRootCoeff F n s hij) := by
  unfold leftSimpleRootCoeff leftResidual
  exact upperElementary_rightExtraction
    (Matrix.GeneralLinearGroup.bruhatLeft s) hij

theorem leftResidual_of_zero
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) (hZero : leftSimpleRootCoeff F n s hij = 0) :
    leftResidual F n s hij = Matrix.GeneralLinearGroup.bruhatLeft s := by
  unfold leftResidual
  exact upperElementaryRightResidual_of_zero _ hij hZero

theorem bruhatLeft_coeff_unique
    (s : Matrix.SpecialLinearGroup (Fin n) F) {i j : Fin n}
    (hij : i ⋖ j) {a : F}
    {r : upperElementarySubgroup (Fin n) F}
    (hrZero : (((r : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j = 0))
    (hEq : Matrix.GeneralLinearGroup.bruhatLeft s =
        r * UpperElementary.elementary i j hij.lt a) :
    a = leftSimpleRootCoeff F n s hij := by
  unfold leftSimpleRootCoeff
  exact upperElementary_rightCoeff_unique
    (Matrix.GeneralLinearGroup.bruhatLeft s) hij hrZero hEq

end LeftCoeff

section FactorizationHelpers

variable {F : Type*} [Field F] {n : ℕ}
variable (s : Matrix.SpecialLinearGroup (Fin n) F)
variable {i j : Fin n} (hij : i ⋖ j)

theorem bruhat_factorization_leftExtract :
    s = UpperElementary.toSLHom
          (leftResidual F n s hij *
            UpperElementary.elementary i j hij.lt
              (leftSimpleRootCoeff F n s hij)) *
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.bruhatMiddle s) *
        UpperElementary.toSLHom
          (Matrix.GeneralLinearGroup.bruhatRight s) := by
  have hS := Matrix.GeneralLinearGroup.bruhat_factorizationSL s
  have hL := bruhatLeft_eq_residual_mul_elementary F n s hij
  calc s = UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatLeft s) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := hS
    _ = UpperElementary.toSLHom
            (leftResidual F n s hij *
              UpperElementary.elementary i j hij.lt
                (leftSimpleRootCoeff F n s hij)) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by rw [hL]

theorem bruhat_factorization_leftExtract' :
    s = UpperElementary.toSLHom (leftResidual F n s hij) *
        UpperElementary.toSLHom
          (UpperElementary.elementary i j hij.lt
            (leftSimpleRootCoeff F n s hij)) *
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.bruhatMiddle s) *
        UpperElementary.toSLHom
          (Matrix.GeneralLinearGroup.bruhatRight s) := by
  have h := bruhat_factorization_leftExtract s hij
  calc s = UpperElementary.toSLHom
            (leftResidual F n s hij *
              UpperElementary.elementary i j hij.lt
                (leftSimpleRootCoeff F n s hij)) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := h
    _ = UpperElementary.toSLHom (leftResidual F n s hij) *
          UpperElementary.toSLHom
            (UpperElementary.elementary i j hij.lt
              (leftSimpleRootCoeff F n s hij)) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
        rw [map_mul]

end FactorizationHelpers

section ZeroBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_weyl_left_zeroCoeff
    (hZero : leftSimpleRootCoeff F n s hij = 0) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
        Matrix.GeneralLinearGroup.bruhatMiddle s := by
  have hRZeroMat : (((leftResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    leftResidual_zero F n s hij
  have hEltZero : UpperElementary.elementary i j hij.lt
      (leftSimpleRootCoeff F n s hij) = 1 := by
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one hij
  have hFactor := bruhat_factorization_leftExtract s hij
  have hFactor' := bruhat_factorization_leftExtract' s hij
  have hSLFactor :
      s = UpperElementary.toSLHom (leftResidual F n s hij) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
    calc s = UpperElementary.toSLHom (leftResidual F n s hij) *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt
                (leftSimpleRootCoeff F n s hij)) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := hFactor'
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            (UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt
                  (leftSimpleRootCoeff F n s hij)) *
              monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s)) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [hEltZero, map_one, one_mul]
  obtain ⟨t', ht'⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_left
      hij (1 : Fˣ) hij.ne (leftResidual F n s hij) hRZeroMat
  have ht'Eq : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
      UpperElementary.toSLHom (leftResidual F n s hij) =
      UpperElementary.toSLHom t' *
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) := ht'
  have hWeylMonomial :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) =
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ)
  have hMulWeyl : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.bruhatMiddle s) =
      monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
          Matrix.GeneralLinearGroup.bruhatMiddle s) := by
    rw [hWeylMonomial, map_mul]
  have hFinalFactor :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
              Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
    have h1 : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s) *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s)) :=
      congrArg
        (fun z => Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * z)
        hSLFactor
    calc Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s
        = Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              monomialSLHom F (Fin n)
                (Matrix.GeneralLinearGroup.bruhatMiddle s) *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s)) := h1
      _ = (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            UpperElementary.toSLHom (leftResidual F n s hij)) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = (UpperElementary.toSLHom t' *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ)) *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by rw [ht'Eq]
      _ = UpperElementary.toSLHom t' *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            monomialSLHom F (Fin n)
              (Matrix.GeneralLinearGroup.bruhatMiddle s)) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
              Matrix.GeneralLinearGroup.bruhatMiddle s) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by rw [hMulWeyl]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s)
    t'
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
      Matrix.GeneralLinearGroup.bruhatMiddle s)
    (Matrix.GeneralLinearGroup.bruhatRight s) hFinalFactor

end ZeroBranch

section PositiveBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_weyl_left_posPerm
    (hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm i <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm j) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
        Matrix.GeneralLinearGroup.bruhatMiddle s := by
  let M := Matrix.GeneralLinearGroup.bruhatMiddle s
  have hResZero : (((leftResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    leftResidual_zero F n s hij
  have hFactor' := bruhat_factorization_leftExtract' s hij
  let c := leftSimpleRootCoeff F n s hij
  let E : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary i j hij.lt c
  let scaled : F :=
    (((M.1.left i)⁻¹ : Fˣ).val * c * (M.1.left j : F))
  let E' : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary
      (M.1.right.symm i) (M.1.right.symm j) hPerm scaled
  have hConj : UpperElementary.toSLHom E *
      monomialSLHom F (Fin n) M =
      monomialSLHom F (Fin n) M * UpperElementary.toSLHom E' := by
    have hTrans : UpperElementary.toSLHom E =
        Matrix.SpecialLinearGroup.transvection hij.ne c := by
      apply toSLHom_elementary_eq_transvection
    have hTrans' : UpperElementary.toSLHom E' =
        Matrix.SpecialLinearGroup.transvection
          (ne_of_lt hPerm) scaled := by
      apply toSLHom_elementary_eq_transvection
    have hConjTrans :=
      transvection_mul_monomialSLHom_eq (R := F) M hij.ne c
    calc UpperElementary.toSLHom E * monomialSLHom F (Fin n) M
        = Matrix.SpecialLinearGroup.transvection hij.ne c *
            monomialSLHom F (Fin n) M := by rw [hTrans]
      _ = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection
              (fun h => hij.ne
                (Equiv.injective (Equiv.symm M.1.right) h))
              scaled := hConjTrans
      _ = monomialSLHom F (Fin n) M * UpperElementary.toSLHom E' := by
          rw [← hTrans']
  let newRight : upperElementarySubgroup (Fin n) F :=
    E' * Matrix.GeneralLinearGroup.bruhatRight s
  have hSNew :
      s = UpperElementary.toSLHom (leftResidual F n s hij) *
        monomialSLHom F (Fin n) M *
        UpperElementary.toSLHom newRight := by
    calc s = UpperElementary.toSLHom (leftResidual F n s hij) *
            UpperElementary.toSLHom E *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          have : E = UpperElementary.elementary i j hij.lt
              (leftSimpleRootCoeff F n s hij) := rfl
          calc s = UpperElementary.toSLHom (leftResidual F n s hij) *
                  UpperElementary.toSLHom
                    (UpperElementary.elementary i j hij.lt
                      (leftSimpleRootCoeff F n s hij)) *
                  monomialSLHom F (Fin n) M *
                  UpperElementary.toSLHom
                    (Matrix.GeneralLinearGroup.bruhatRight s) := hFactor'
            _ = UpperElementary.toSLHom (leftResidual F n s hij) *
                  UpperElementary.toSLHom E *
                  monomialSLHom F (Fin n) M *
                  UpperElementary.toSLHom
                    (Matrix.GeneralLinearGroup.bruhatRight s) := rfl
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            (UpperElementary.toSLHom E * monomialSLHom F (Fin n) M) *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            (monomialSLHom F (Fin n) M * UpperElementary.toSLHom E') *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [hConj]
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            monomialSLHom F (Fin n) M *
            (UpperElementary.toSLHom E' *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s)) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom newRight := by
          rw [map_mul]
  obtain ⟨t', ht'⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_left
      hij (1 : Fˣ) hij.ne (leftResidual F n s hij) hResZero
  have ht'Eq : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
      UpperElementary.toSLHom (leftResidual F n s hij) =
      UpperElementary.toSLHom t' *
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) := ht'
  have hWeylMonomial :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) =
        monomialSLHom F (Fin n)
          (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ)
  have hMulWeyl : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
        monomialSLHom F (Fin n) M =
      monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * M) := by
    rw [hWeylMonomial, map_mul]
  have hFinalFactor :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * M) *
          UpperElementary.toSLHom newRight := by
    have h1 : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom newRight) :=
      congrArg
        (fun z => Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * z)
        hSNew
    calc Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s
        = Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom newRight) := h1
      _ = (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            UpperElementary.toSLHom (leftResidual F n s hij)) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom newRight := by
          simp only [mul_assoc]
      _ = (UpperElementary.toSLHom t' *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ)) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom newRight := by rw [ht'Eq]
      _ = UpperElementary.toSLHom t' *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom newRight := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * M) *
          UpperElementary.toSLHom newRight := by rw [hMulWeyl]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s)
    t'
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * M)
    newRight hFinalFactor

end PositiveBranch

section NegativeBranch

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

theorem bruhatMiddle_weyl_left_negPerm
    (v : Fˣ) (hv : leftSimpleRootCoeff F n s hij = -(v : F))
    (hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm j <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm i) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ *
        Matrix.GeneralLinearGroup.bruhatMiddle s := by
  let M := Matrix.GeneralLinearGroup.bruhatMiddle s
  have hResZero : (((leftResidual F n s hij :
      Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    leftResidual_zero F n s hij
  have hFactor' := bruhat_factorization_leftExtract' s hij
  have hEeq : UpperElementary.elementary i j hij.lt
      (leftSimpleRootCoeff F n s hij) =
      UpperElementary.elementary i j hij.lt (-(v : F)) := by
    rw [hv]
  have hRankOne :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F)) =
      Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
        (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
        Matrix.SpecialLinearGroup.transvection hij.ne.symm (-(↑v⁻¹ : F)) :=
    weylSLUnit_one_mul_transvection_neg hij.ne v
  have hTransE : UpperElementary.toSLHom
      (UpperElementary.elementary i j hij.lt (-(v : F))) =
      Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F)) := by
    apply toSLHom_elementary_eq_transvection
  obtain ⟨tRes, htRes⟩ :=
    Matrix.GeneralLinearGroup.weylSLUnit_mul_toSLHom_exists_left
      hij (1 : Fˣ) hij.ne (leftResidual F n s hij) hResZero
  have htResEq : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
      UpperElementary.toSLHom (leftResidual F n s hij) =
      UpperElementary.toSLHom tRes *
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) := htRes
  let scaledLower : F :=
    (((M.1.left j)⁻¹ : Fˣ).val * (-(↑v⁻¹ : F)) * (M.1.left i : F))
  let lowerConj : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary (M.1.right.symm j) (M.1.right.symm i)
      hPerm scaledLower
  have hLowerConj :
      Matrix.SpecialLinearGroup.transvection hij.ne.symm (-(↑v⁻¹ : F)) *
          monomialSLHom F (Fin n) M =
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj := by
    have hConj :=
      transvection_mul_monomialSLHom_eq (R := F) M hij.ne.symm (-(↑v⁻¹ : F))
    have hToSL : UpperElementary.toSLHom lowerConj =
        Matrix.SpecialLinearGroup.transvection
          (ne_of_lt hPerm) scaledLower := by
      apply toSLHom_elementary_eq_transvection
    have hEq : Matrix.SpecialLinearGroup.transvection
          (fun h => hij.ne.symm
            (Equiv.injective (Equiv.symm M.1.right) h))
          ((((M.1.left j)⁻¹ : Fˣ).val * (-(↑v⁻¹ : F)) * (M.1.left i : F))) =
        UpperElementary.toSLHom lowerConj := by
      rw [← hToSL]
    calc Matrix.SpecialLinearGroup.transvection hij.ne.symm (-(↑v⁻¹ : F)) *
            monomialSLHom F (Fin n) M
        = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection
              (fun h => hij.ne.symm
                (Equiv.injective (Equiv.symm M.1.right) h))
              ((((M.1.left j)⁻¹ : Fˣ).val * (-(↑v⁻¹ : F)) *
                (M.1.left i : F))) := hConj
      _ = monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj := by
          rw [← hEq]
  let newLeft : upperElementarySubgroup (Fin n) F :=
    tRes * UpperElementary.elementary i j hij.lt (↑v⁻¹ : F)
  let newRight : upperElementarySubgroup (Fin n) F :=
    lowerConj * Matrix.GeneralLinearGroup.bruhatRight s
  have hTorusMonomialInv :
      (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ =
        monomialSLHom F (Fin n)
          ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹) := by
    rw [Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom, map_inv]
  have hM_TorusInv : (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
        monomialSLHom F (Fin n) M =
      monomialSLHom F (Fin n)
        ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) := by
    rw [hTorusMonomialInv, map_mul]
  have hS_decomp :
      s = UpperElementary.toSLHom (leftResidual F n s hij) *
          UpperElementary.toSLHom
            (UpperElementary.elementary i j hij.lt (-(v : F))) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
    calc s = UpperElementary.toSLHom (leftResidual F n s hij) *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt
                (leftSimpleRootCoeff F n s hij)) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := hFactor'
      _ = UpperElementary.toSLHom (leftResidual F n s hij) *
            UpperElementary.toSLHom
              (UpperElementary.elementary i j hij.lt (-(v : F))) *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [hEeq]
  have hFinal :
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) *
          UpperElementary.toSLHom newRight := by
    have h1 : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s =
        Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt (-(v : F))) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s)) :=
      congrArg
        (fun z => Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * z)
        hS_decomp
    have hT1 : UpperElementary.toSLHom
          (UpperElementary.elementary i j hij.lt (↑v⁻¹ : F)) =
        Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) := by
      apply toSLHom_elementary_eq_transvection
    calc Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s
        = Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            (UpperElementary.toSLHom (leftResidual F n s hij) *
              UpperElementary.toSLHom
                (UpperElementary.elementary i j hij.lt (-(v : F))) *
              monomialSLHom F (Fin n) M *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s)) := h1
      _ = (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            UpperElementary.toSLHom (leftResidual F n s hij)) *
          UpperElementary.toSLHom
            (UpperElementary.elementary i j hij.lt (-(v : F))) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = (UpperElementary.toSLHom tRes *
            Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ)) *
          Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F)) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [htResEq, ← hTransE]
      _ = UpperElementary.toSLHom tRes *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F))) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          (Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
            (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
            Matrix.SpecialLinearGroup.transvection hij.ne.symm (-(↑v⁻¹ : F))) *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [hRankOne]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
          (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
          (Matrix.SpecialLinearGroup.transvection hij.ne.symm (-(↑v⁻¹ : F)) *
            monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
          (Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
          (monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj) *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          rw [hLowerConj]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
          ((Matrix.GeneralLinearGroup.torusSLUnit i j hij.ne v)⁻¹ *
            monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom lowerConj *
          UpperElementary.toSLHom
            (Matrix.GeneralLinearGroup.bruhatRight s) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
          monomialSLHom F (Fin n)
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) *
          (UpperElementary.toSLHom lowerConj *
            UpperElementary.toSLHom
              (Matrix.GeneralLinearGroup.bruhatRight s)) := by
          rw [hM_TorusInv]
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) *
          monomialSLHom F (Fin n)
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) *
          UpperElementary.toSLHom newRight := by
          rw [show UpperElementary.toSLHom lowerConj *
              UpperElementary.toSLHom
                (Matrix.GeneralLinearGroup.bruhatRight s) =
              UpperElementary.toSLHom newRight from by
                simp [newRight, map_mul]]
      _ = (UpperElementary.toSLHom tRes *
            Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F)) *
          monomialSLHom F (Fin n)
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) *
          UpperElementary.toSLHom newRight := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n)
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M) *
          UpperElementary.toSLHom newRight := by
          rw [show UpperElementary.toSLHom tRes *
              Matrix.SpecialLinearGroup.transvection hij.ne (↑v⁻¹ : F) =
              UpperElementary.toSLHom newLeft from by
                rw [← hT1, map_mul]]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s)
    newLeft
    ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ * M)
    newRight hFinal

end NegativeBranch

section Exhaustive

variable {F : Type*} [Field F] {n : ℕ}
variable {i j : Fin n} (hij : i ⋖ j)
variable (s : Matrix.SpecialLinearGroup (Fin n) F)

noncomputable def torusUnitOfNegCoeff
    (c : F) (hc : c ≠ 0) : Fˣ :=
  Units.mk0 (-c) (neg_ne_zero.mpr hc)

theorem torusUnitOfNegCoeff_val (c : F) (hc : c ≠ 0) :
    (torusUnitOfNegCoeff c hc : F) = -c := by
  simp [torusUnitOfNegCoeff]

theorem torusUnitOfNegCoeff_spec (c : F) (hc : c ≠ 0) :
    c = -((torusUnitOfNegCoeff c hc : F)) := by
  have h := torusUnitOfNegCoeff_val c hc
  have : (torusUnitOfNegCoeff c hc : F) = -c := h
  calc c = -(-c) := by simp
    _ = -((torusUnitOfNegCoeff c hc : F)) := by rw [this]

theorem torusUnitOfNegCoeff_unique (c : F) (hc : c ≠ 0) (v : Fˣ)
    (hv : c = -(v : F)) :
    v = torusUnitOfNegCoeff c hc := by
  apply Units.ext
  simp [torusUnitOfNegCoeff, hv]

theorem bruhatLeftTransition_cases :
    (leftSimpleRootCoeff F n s hij = 0 ∧
      Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
        Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
          Matrix.GeneralLinearGroup.bruhatMiddle s) ∨
    ((Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm i <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm j ∧
      Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
        Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
          Matrix.GeneralLinearGroup.bruhatMiddle s) ∨
    (∃ v : Fˣ, leftSimpleRootCoeff F n s hij = -(v : F) ∧
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm j <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm i ∧
        Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
          (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ *
            Matrix.GeneralLinearGroup.bruhatMiddle s) := by
  by_cases hZero : leftSimpleRootCoeff F n s hij = 0
  · exact Or.inl ⟨hZero, bruhatMiddle_weyl_left_zeroCoeff hij s hZero⟩
  · by_cases hPerm : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right.symm i <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
              MonomialBase Fˣ (Fin n)).right.symm j
    · exact Or.inr (Or.inl ⟨hPerm,
        bruhatMiddle_weyl_left_posPerm hij s hPerm⟩)
    · have hNotPos : ¬ (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right.symm i <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
              MonomialBase Fˣ (Fin n)).right.symm j := hPerm
      have hNe : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right.symm i ≠
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm j := by
        intro heq
        have hinj := Equiv.injective
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm
        have hijNe : i ≠ j := hij.ne
        exact hijNe (hinj heq)
      have hNeg : (Matrix.GeneralLinearGroup.bruhatMiddle s :
          MonomialBase Fˣ (Fin n)).right.symm j <
          (Matrix.GeneralLinearGroup.bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm i := by
        have hTotal := lt_or_gt_of_ne hNe
        rcases hTotal with hLt | hGt
        · exact absurd hLt hNotPos
        · exact hGt
      have hcNe : leftSimpleRootCoeff F n s hij ≠ 0 := hZero
      let v := torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hcNe
      have hv : leftSimpleRootCoeff F n s hij = -(v : F) :=
        torusUnitOfNegCoeff_spec _ hcNe
      refine Or.inr (Or.inr ⟨v, hv, hNeg, ?_⟩)
      exact bruhatMiddle_weyl_left_negPerm hij s v hv hNeg

end Exhaustive

section AdjacentLowerRootBranchAPI

variable {F : Type*} [Field F] {n : ℕ}

theorem bruhatMiddle_transvection_neg_mul_weylSLUnit_inv
    {i j : Fin n} (hij : i ⋖ j) (r : F) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) =
      (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
  let L : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary i j hij.lt (-r)
  let M : MonomialSL F (Fin n) :=
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹
  let R : upperElementarySubgroup (Fin n) F := 1
  have hTrans : Matrix.SpecialLinearGroup.transvection hij.ne (-r) =
      UpperElementary.toSLHom L := by
    apply Subtype.ext
    simp [L, Matrix.SpecialLinearGroup.transvection_coe,
      UpperElementary.coe_toSLHom, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary]
  have hWeyl : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) =
      monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ)
  have hWeylInv : (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ =
      monomialSLHom F (Fin n) M := by
    have hInv : (monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)))⁻¹ =
        monomialSLHom F (Fin n) M := by
      rw [← map_inv]
    calc (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹
        = (monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)))⁻¹ := by
          rw [← hWeyl]
      _ = monomialSLHom F (Fin n) M := hInv
  have hFact : Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ =
        UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R := by
    calc Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹
        = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M := by
          rw [hTrans, hWeylInv]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom R := by simp [R]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

theorem leftSimpleRootCoeff_transvection_neg_mul_weylSLUnit_inv
    {i j : Fin n} (hij : i ⋖ j) (r : F) :
    leftSimpleRootCoeff F n
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij = -r := by
  let L : upperElementarySubgroup (Fin n) F :=
    UpperElementary.elementary i j hij.lt (-r)
  let M : MonomialSL F (Fin n) :=
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹
  let R : upperElementarySubgroup (Fin n) F := 1
  have hTrans : Matrix.SpecialLinearGroup.transvection hij.ne (-r) =
      UpperElementary.toSLHom L := by
    apply Subtype.ext
    simp [L, Matrix.SpecialLinearGroup.transvection_coe,
      UpperElementary.coe_toSLHom, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary]
  have hWeyl : Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) =
      monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)) :=
    Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ)
  have hWeylInv : (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ =
      monomialSLHom F (Fin n) M := by
    have hInv : (monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)))⁻¹ =
        monomialSLHom F (Fin n) M := by
      rw [← map_inv]
    calc (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹
        = (monomialSLHom F (Fin n)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)))⁻¹ := by
          rw [← hWeyl]
      _ = monomialSLHom F (Fin n) M := hInv
  have hFact : Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ =
        UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R := by
    calc Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹
        = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M := by
          rw [hTrans, hWeylInv]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom R := by simp [R]
  have hWeylRight : (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) :
      MonomialBase Fˣ (Fin n)).right = Equiv.swap i j := by
    simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hMRight : (M : MonomialBase Fˣ (Fin n)).right = Equiv.swap i j := by
    calc (M : MonomialBase Fˣ (Fin n)).right
        = ((Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹ :
            MonomialBase Fˣ (Fin n)).right := rfl
      _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) :
            MonomialBase Fˣ (Fin n)).right⁻¹ := by
          rw [Matrix.GeneralLinearGroup.monomialBase_inv_right]
      _ = Equiv.swap i j := by rw [hWeylRight, Equiv.swap_inv]
  have hMRightInv : (M : MonomialBase Fˣ (Fin n)).right⁻¹ = Equiv.swap i j := by
    rw [hMRight, Equiv.swap_inv]
  have hNeg : (M : MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (M : MonomialBase Fˣ (Fin n)).right⁻¹ i := by
    rw [hMRightInv, Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact hij.lt
  have hEntry : (((L : Matrix.GeneralLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j) = -r := by
    have hNe : i ≠ j := hij.ne
    simp [L, UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, hNe]
  have hLeftEq := Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact hij hNeg
  have hCoeff : leftSimpleRootCoeff F n
      (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
        (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij =
      (((Matrix.GeneralLinearGroup.bruhatLeft
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
        Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := rfl
  calc leftSimpleRootCoeff F n
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
            (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
          Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := by
        rw [← hLeftEq]
    _ = -r := hEntry

theorem bruhatMiddle_transvection_neg_mul_weylSLUnit_inv_not_pos
    {i j : Fin n} (hij : i ⋖ j) (r : F) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
        MonomialBase Fˣ (Fin n)).right.symm i <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
          (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
        MonomialBase Fˣ (Fin n)).right.symm j) := by
  have hMid := bruhatMiddle_transvection_neg_mul_weylSLUnit_inv (F := F) hij r
  rw [hMid]
  let M : MonomialSL F (Fin n) :=
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹
  have hWeylRight : (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) :
      MonomialBase Fˣ (Fin n)).right = Equiv.swap i j := by
    simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hMRight : (M : MonomialBase Fˣ (Fin n)).right = Equiv.swap i j := by
    calc (M : MonomialBase Fˣ (Fin n)).right
        = ((Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ))⁻¹ :
            MonomialBase Fˣ (Fin n)).right := rfl
      _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) :
            MonomialBase Fˣ (Fin n)).right⁻¹ := by
          rw [Matrix.GeneralLinearGroup.monomialBase_inv_right]
      _ = Equiv.swap i j := by rw [hWeylRight, Equiv.swap_inv]
  have hEq : (M : MonomialBase Fˣ (Fin n)).right.symm = Equiv.swap i j := by
    have h1 : (M : MonomialBase Fˣ (Fin n)).right⁻¹ = Equiv.swap i j := by
      rw [hMRight, Equiv.swap_inv]
    have h2 : (M : MonomialBase Fˣ (Fin n)).right.symm =
        (M : MonomialBase Fˣ (Fin n)).right⁻¹ := rfl
    rw [h2, h1]
  have hSymI : (M : MonomialBase Fˣ (Fin n)).right.symm i = j := by
    rw [hEq, Equiv.swap_apply_left]
  have hSymJ : (M : MonomialBase Fˣ (Fin n)).right.symm j = i := by
    rw [hEq, Equiv.swap_apply_right]
  have hChange : ((M : MonomialBase Fˣ (Fin n)).right.symm i <
      (M : MonomialBase Fˣ (Fin n)).right.symm j) = (j < i) := by
    rw [hSymI, hSymJ]
  have hNot : ¬ (j < i) := not_lt_of_gt hij.lt
  intro hLt
  have hJltI : j < i := by
    have h1 : (M : MonomialBase Fˣ (Fin n)).right.symm i <
        (M : MonomialBase Fˣ (Fin n)).right.symm j := hLt
    rw [hSymI, hSymJ] at h1
    exact h1
  exact hNot hJltI

end AdjacentLowerRootBranchAPI

section FirstTranslatedBruhat

variable {F : Type*} [Field F]

noncomputable def fin3TranslatedLowerCycleMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)

private noncomputable def L0Fin3 (F : Type*) [Field F] : upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)

private noncomputable def R0Fin3 (F : Type*) [Field F] : upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : F)

private noncomputable def L1Fin3 (F : Type*) [Field F] : upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F)

private theorem fin3TranslatedLowerCycleMonomial_right_perm (F : Type*) [Field F] :
    (fin3TranslatedLowerCycleMonomial F : MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  unfold fin3TranslatedLowerCycleMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
        Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3TranslatedLowerCycleMonomial_inv_perm (F : Type*) [Field F] :
    (fin3TranslatedLowerCycleMonomial F : MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  have h := fin3TranslatedLowerCycleMonomial_right_perm (F := F)
  have hInv : (fin3TranslatedLowerCycleMonomial (F := F) : MonomialBase Fˣ (Fin 3)).right⁻¹ =
      (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)⁻¹ := by rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

private theorem weyl_ne_irrel {F : Type*} [Field F] {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
    Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit, Matrix.SpecialLinearGroup.transvection_coe]

private theorem transvection_ne_irrel
    {F : Type*} [Field F] {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
    Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

private theorem S0_factorization_aux (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
    UpperElementary.toSLHom (L0Fin3 F) *
      monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
      UpperElementary.toSLHom (R0Fin3 F) := by
  have hWInv : (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
      Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
            rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
            apply weyl_ne_irrel
  have hM : monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) =
      Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
      Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)) := by
            unfold fin3TranslatedLowerCycleMonomial; rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
            rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
                Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 : UpperElementary.toSLHom (L0Fin3 (F := F)) =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold L0Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hR0 : UpperElementary.toSLHom (R0Fin3 (F := F)) =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 3) ≠ 1) (-1 : F) := by
    unfold R0Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hT10 : Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 3) ≠ 0) (-1 : F) := by
    apply transvection_ne_irrel
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 0) (-1 : F) := by
          rw [hWInv, hT10]
    _ = UpperElementary.toSLHom (L0Fin3 F) *
        monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
        UpperElementary.toSLHom (R0Fin3 F) := by
          rw [hM, hL0, hR0]
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.weylSLUnit,
                  Matrix.SpecialLinearGroup.transvection_coe,
                  Matrix.SpecialLinearGroup.coe_mul,
                  Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Matrix.mul_apply,
                  Fin.sum_univ_three, Fin.isValue]

private theorem S1_factorization_aux (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
    UpperElementary.toSLHom (L1Fin3 F) *
      monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
      UpperElementary.toSLHom (R0Fin3 F) := by
  have hS0 := S0_factorization_aux (F := F) h01 h12
  have hT12L0 :
      Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
        UpperElementary.toSLHom (L0Fin3 F) =
      UpperElementary.toSLHom (L1Fin3 F) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L0Fin3, L1Fin3, UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
        Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue]
  calc Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)
      = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) := by
          simp only [mul_assoc]
    _ = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
        (UpperElementary.toSLHom (L0Fin3 F) *
          monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
          UpperElementary.toSLHom (R0Fin3 F)) := by
          rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          UpperElementary.toSLHom (L0Fin3 F)) *
        monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
        UpperElementary.toSLHom (R0Fin3 F) := by
          simp only [mul_assoc]
    _ = UpperElementary.toSLHom (L1Fin3 F) *
        monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) *
        UpperElementary.toSLHom (R0Fin3 F) := by
          rw [hT12L0]

theorem leftSimpleRootCoeff_weyl12_inv_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
      ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
       Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) h12 = 0 := by
  have hFact := S0_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3TranslatedLowerCycleMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3TranslatedLowerCycleMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3TranslatedLowerCycleMonomial_inv_perm]
    decide
  have hEntry :
      (((L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
    simp [L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F)) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := by
          rw [hLeftEq]
    _ = 0 := hEntry

theorem leftSimpleRootCoeff_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
      (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
       (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
       Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) h12 = 1 := by
  have hFact := S1_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3TranslatedLowerCycleMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3TranslatedLowerCycleMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3TranslatedLowerCycleMonomial_inv_perm]
    decide
  have hEntry :
      (((L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2 = 1) := by
    have hMul := upperElementary_covBy_mul_entry
      (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : F))
      (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F))
      (show (1 : Fin 3) ⋖ (2 : Fin 3) from h12)
    have hL1eq : L1Fin3 (F := F) =
        UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) := rfl
    rw [hL1eq, hMul]
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F)) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := by
          rw [hLeftEq]
    _ = 1 := hEntry

theorem bruhatMiddle_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
       (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
       Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) =
      fin3TranslatedLowerCycleMonomial F := by
  have hFact := S1_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ _ _ _ hFact

theorem bruhatMiddle_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
         (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
         Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
         (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
         Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
      (F := F) h01 h12
  rw [hMid, fin3TranslatedLowerCycleMonomial_right_perm]
  decide

theorem bruhatMiddle_weyl12_inv_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
       Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) =
      fin3TranslatedLowerCycleMonomial F := by
  have hFact := S0_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ _ _ _ hFact

end FirstTranslatedBruhat

section StageThreeTranslatedBruhat

variable {F : Type*} [Field F]

noncomputable def fin3LowerStageThreeMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
    (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)

private noncomputable def L30Fin3 (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F)

private noncomputable def R30Fin3 (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (-1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private theorem fin3LowerStageThreeMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3LowerStageThreeMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 2 := by
  unfold fin3LowerStageThreeMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3LowerStageThreeMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3LowerStageThreeMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 2 := by
  have h := fin3LowerStageThreeMonomial_right_perm (F := F)
  have hInv :
      (fin3LowerStageThreeMonomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, Equiv.swap_inv]

private theorem stageThree_S30_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection
          h12.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection
          h01.ne.symm (-1 : F)) =
    UpperElementary.toSLHom (L30Fin3 F) *
      monomialSLHom F (Fin 3)
        (fin3LowerStageThreeMonomial F) *
      UpperElementary.toSLHom (R30Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply weyl_ne_irrel
  have hWeyl02 :
      monomialSLHom F (Fin 3)
          (fin3LowerStageThreeMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    unfold fin3LowerStageThreeMonomial
    rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hT21 :
      Matrix.SpecialLinearGroup.transvection
          h12.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (-1 : F) := by
    apply transvection_ne_irrel
  have hT10 :
      Matrix.SpecialLinearGroup.transvection
          h01.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 0) (-1 : F) := by
    apply transvection_ne_irrel
  have hL30 :
      UpperElementary.toSLHom (L30Fin3 F) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (1 : F) := by
    unfold L30Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR30 :
      UpperElementary.toSLHom (R30Fin3 F) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold R30Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            h12.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            h01.ne.symm (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 0) (-1 : F)) := by
        rw [hWInv, hT21, hT10]
    _ = UpperElementary.toSLHom (L30Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3LowerStageThreeMonomial F) *
          UpperElementary.toSLHom (R30Fin3 F) := by
        rw [hL30, hR30, hWeyl02]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem stageThree_S31_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            h12.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            h01.ne.symm (-1 : F))) =
    UpperElementary.toSLHom
        (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) * L30Fin3 F) *
      monomialSLHom F (Fin 3)
        (fin3LowerStageThreeMonomial F) *
      UpperElementary.toSLHom (R30Fin3 F) := by
  have hS30 := stageThree_S30_factorization_aux (F := F) h01 h12
  have hTrans01 :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (-1 : F) := by
          apply transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (UpperElementary.toSLHom (L30Fin3 F) *
            monomialSLHom F (Fin 3)
              (fin3LowerStageThreeMonomial F) *
            UpperElementary.toSLHom (R30Fin3 F)) := by
        rw [hS30]
    _ = (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          UpperElementary.toSLHom (L30Fin3 F)) *
          monomialSLHom F (Fin 3)
            (fin3LowerStageThreeMonomial F) *
          UpperElementary.toSLHom (R30Fin3 F) := by
        simp only [mul_assoc]
    _ = (UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F)) *
          UpperElementary.toSLHom (L30Fin3 F)) *
          monomialSLHom F (Fin 3)
            (fin3LowerStageThreeMonomial F) *
          UpperElementary.toSLHom (R30Fin3 F) := by
        rw [hTrans01]
    _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F) * L30Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3LowerStageThreeMonomial F) *
          UpperElementary.toSLHom (R30Fin3 F) := by
        rw [← map_mul]

theorem bruhatMiddle_weyl01_inv_mul_transvection21_neg_one_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F))) =
      fin3LowerStageThreeMonomial F := by
  have hFact := stageThree_S30_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection21_neg_one_mul_transvection10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F))) h01 = 0 := by
  have hFact := stageThree_S30_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3LowerStageThreeMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3LowerStageThreeMonomial F :
            MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3LowerStageThreeMonomial_inv_perm]
    decide
  have hEntry :
      ((((L30Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) = 0) := by
    have hMul := upperElementary_covBy_mul_entry
      (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
        (by decide) (1 : F))
      (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) (1 : F))
      (show (0 : Fin 3) ⋖ (1 : Fin 3) from h01)
    have hL30eq : L30Fin3 (F := F) =
        UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
          (by decide) (1 : F) *
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (1 : F) := rfl
    rw [hL30eq, hMul]
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F))) h01
      = ((((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  h12.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  h01.ne.symm (-1 : F))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1)) := rfl
    _ = ((((L30Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1)) := by
        rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F)))) =
      fin3LowerStageThreeMonomial F := by
  have hFact := stageThree_S31_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F)))) h01 = -1 := by
  have hFact := stageThree_S31_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3LowerStageThreeMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3LowerStageThreeMonomial F :
            MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3LowerStageThreeMonomial_inv_perm]
    decide
  have hEntry :
      ((((UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) * L30Fin3 F :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) = -1) := by
    simp [L30Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply, Fin.isValue]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F)))) h01
      = ((((Matrix.GeneralLinearGroup.bruhatLeft
            (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit
                  (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    h12.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    h01.ne.symm (-1 : F)))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1)) := rfl
    _ = ((((UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) * L30Fin3 F :
          upperElementarySubgroup (Fin 3) F) :
        Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeftEq]
    _ = -1 := hEntry

theorem bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one
      (F := F) h01 h12
  have hEq :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))) := by
    simp only [mul_assoc]
  rw [hEq, hMid, fin3LowerStageThreeMonomial_right_perm]
  decide

end StageThreeTranslatedBruhat

section StageFourTranslatedBruhat

variable {F : Type*} [Field F]

noncomputable def fin3LowerStageFourMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)

private noncomputable def L40Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def R40Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F)

private theorem fin3LowerStageFourMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3LowerStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  unfold fin3LowerStageFourMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3LowerStageFourMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3LowerStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  have h := fin3LowerStageFourMonomial_right_perm (F := F)
  have hInv :
      (fin3LowerStageFourMonomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

private theorem stageFour_S40_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
        Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)) =
    UpperElementary.toSLHom (L40Fin3 F) *
      monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
      UpperElementary.toSLHom (R40Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)) := by
          unfold fin3LowerStageFourMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hT10_one :
      Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 0) (1 : F) := by
    apply transvection_ne_irrel
  have hT21_neg :
      Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (-1 : F) := by
    apply transvection_ne_irrel
  have hT10_neg :
      Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 0) (-1 : F) := by
    apply transvection_ne_irrel
  have hL40 :
      UpperElementary.toSLHom (L40Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (-1 : F) := by
    unfold L40Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR40 :
      UpperElementary.toSLHom (R40Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (1 : F) := by
    unfold R40Fin3
    rw [toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 0) (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 0) (-1 : F)) := by
        rw [hWInv, hT10_one, hT21_neg, hT10_neg]
    _ = UpperElementary.toSLHom (L40Fin3 F) *
          monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
          UpperElementary.toSLHom (R40Fin3 F) := by
        rw [hL40, hR40, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

theorem bruhatMiddle_weyl12_inv_transvection10_1_transvection21_neg1_transvection10_neg1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))) =
      fin3LowerStageFourMonomial F := by
  have hFact := stageFour_S40_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_weyl12_inv_transvection10_1_transvection21_neg1_transvection10_neg1_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) := by
  have hMid :=
    bruhatMiddle_weyl12_inv_transvection10_1_transvection21_neg1_transvection10_neg1
      (F := F) h01 h12
  rw [hMid, fin3LowerStageFourMonomial_right_perm]
  decide

private noncomputable def L41Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (-1 : F)

private theorem stageFour_S41_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F))) =
      UpperElementary.toSLHom (L41Fin3 F) *
        monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
        UpperElementary.toSLHom (R40Fin3 F) := by
  have hS40 := stageFour_S40_factorization_aux (F := F) h01 h12
  have hTrans12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (1 : Fin 3) < 2)) (-1 : F) := by
          apply transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hL40_eq :
      L40Fin3 (F := F) =
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (1 : F) *
          UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) := rfl
  have hCancel :
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (-1 : F) *
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (1 : F) = 1 := by
    have hAdd :
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (-1 : F) *
          UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (1 : F) =
          UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) ((-1 : F) + 1) := by
      apply Subtype.ext
      simp [Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hAdd]
    have hZero : ((-1 : F) + 1) = 0 := by simp
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one h12
  have hLeftCancel :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        UpperElementary.toSLHom (L40Fin3 F) =
        UpperElementary.toSLHom (L41Fin3 F) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          UpperElementary.toSLHom (L40Fin3 F)
        = UpperElementary.toSLHom
              (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F)) *
            UpperElementary.toSLHom (L40Fin3 F) := by
          rw [hTrans12]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F) * L40Fin3 F) := by
          rw [← map_mul]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F) *
                (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                  (by decide) (1 : F) *
                UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                  (by decide) (-1 : F))) := by
          rw [hL40_eq]
      _ = UpperElementary.toSLHom
              ((UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F) *
              UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (1 : F)) *
            UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [mul_assoc]
      _ = UpperElementary.toSLHom
              (1 * UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) := by
          rw [hCancel]
      _ = UpperElementary.toSLHom (L41Fin3 F) := by
          simp [L41Fin3]
  calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          (UpperElementary.toSLHom (L40Fin3 F) *
            monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
            UpperElementary.toSLHom (R40Fin3 F)) := by
        rw [hS40]
    _ = (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          UpperElementary.toSLHom (L40Fin3 F)) *
        monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
        UpperElementary.toSLHom (R40Fin3 F) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (L41Fin3 F) *
        monomialSLHom F (Fin 3) (fin3LowerStageFourMonomial F) *
        UpperElementary.toSLHom (R40Fin3 F) := by
        rw [hLeftCancel]

theorem bruhatMiddle_T12_neg1_w12_inv_transvection10_1_transvection21_neg1_transvection10_neg1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)))) =
      fin3LowerStageFourMonomial F := by
  have hFact := stageFour_S41_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_T12_neg1_w12_inv_transvection10_1_transvection21_neg1_transvection10_neg1_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) := by
  have hMid :=
    bruhatMiddle_T12_neg1_w12_inv_transvection10_1_transvection21_neg1_transvection10_neg1
      (F := F) h01 h12
  rw [hMid, fin3LowerStageFourMonomial_right_perm]
  decide

end StageFourTranslatedBruhat

section G01TranslatedBruhat

variable {F : Type*} [Field F]

noncomputable def fin3G01Monomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
    (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)

private theorem fin3G01Monomial_right_perm
    (F : Type*) [Field F] :
    (fin3G01Monomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (1 : Fin 3) 2 := by
  unfold fin3G01Monomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G01Monomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G01Monomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (1 : Fin 3) 2 := by
  have h := fin3G01Monomial_right_perm (F := F)
  have hInv :
      (fin3G01Monomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (1 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, Equiv.swap_inv]

private noncomputable def G01_L1Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary
    (0 : Fin 3) (1 : Fin 3) (by decide) a *
  UpperElementary.elementary
    (0 : Fin 3) (2 : Fin 3) (by decide) a

private noncomputable def G01_L0Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary
    (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
  G01_L1Fin3 F a

private theorem G01_S0_factorization_aux
    (F : Type*) [Field F] (a : F)
    (_h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) =
    UpperElementary.toSLHom (G01_L0Fin3 F a) *
      monomialSLHom F (Fin 3) (fin3G01Monomial F) *
      UpperElementary.toSLHom
        (1 : upperElementarySubgroup (Fin 3) F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3) (fin3G01Monomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    unfold fin3G01Monomial
    rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hT02 :
      Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) (-a) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (-a) := by
    apply transvection_ne_irrel
  have hT21 :
      Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (-1 : F) := by
    apply transvection_ne_irrel
  have hL0 :
      UpperElementary.toSLHom (G01_L0Fin3 (F := F) a) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 1) a *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) a) := by
    unfold G01_L0Fin3 G01_L1Fin3
    rw [map_mul, map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (-1 : F)) := by
          rw [hWInv, hT02, hT21]
    _ = UpperElementary.toSLHom (G01_L0Fin3 F a) *
          monomialSLHom F (Fin 3) (fin3G01Monomial F) *
          UpperElementary.toSLHom
            (1 : upperElementarySubgroup (Fin 3) F) := by
        rw [hL0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G01_S1_factorization_aux
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) =
    UpperElementary.toSLHom (G01_L1Fin3 F a) *
      monomialSLHom F (Fin 3) (fin3G01Monomial F) *
      UpperElementary.toSLHom
        (1 : upperElementarySubgroup (Fin 3) F) := by
  have hS0 := G01_S0_factorization_aux (F := F) a h01 h12
  have hT12 :
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (1 : Fin 3) < 2)) (-1 : F) := by
          apply transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hL1_eq :
      G01_L0Fin3 (F := F) a =
        UpperElementary.elementary
          (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
        G01_L1Fin3 F a := rfl
  have hCancel :
      UpperElementary.elementary
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
        UpperElementary.elementary
          (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) = 1 := by
    have hAdd :
        UpperElementary.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
          UpperElementary.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) =
          UpperElementary.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) ((-1 : F) + 1) := by
      apply Subtype.ext
      simp [Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hAdd]
    have hZero : ((-1 : F) + 1) = 0 := by simp
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one h12
  have hLeftCancel :
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
        UpperElementary.toSLHom (G01_L0Fin3 F a) =
        UpperElementary.toSLHom (G01_L1Fin3 F a) := by
    calc Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          UpperElementary.toSLHom (G01_L0Fin3 F a)
        = UpperElementary.toSLHom
              (UpperElementary.elementary
                (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)) *
            UpperElementary.toSLHom (G01_L0Fin3 F a) := by
          rw [hT12]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary
                  (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
                G01_L0Fin3 F a) := by
          rw [← map_mul]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary
                  (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
                (UpperElementary.elementary
                    (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
                  G01_L1Fin3 F a)) := by
          rw [hL1_eq]
      _ = UpperElementary.toSLHom
              ((UpperElementary.elementary
                  (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F) *
                UpperElementary.elementary
                  (1 : Fin 3) (2 : Fin 3) (by decide) (1 : F)) *
              G01_L1Fin3 F a) := by
          rw [mul_assoc]
      _ = UpperElementary.toSLHom
              (1 * G01_L1Fin3 F a) := by
          rw [hCancel]
      _ = UpperElementary.toSLHom (G01_L1Fin3 F a) := by
          simp
  calc Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          (UpperElementary.toSLHom (G01_L0Fin3 F a) *
            monomialSLHom F (Fin 3) (fin3G01Monomial F) *
            UpperElementary.toSLHom
              (1 : upperElementarySubgroup (Fin 3) F)) := by
          rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          UpperElementary.toSLHom (G01_L0Fin3 F a)) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom
          (1 : upperElementarySubgroup (Fin 3) F) := by
          simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G01_L1Fin3 F a) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom
          (1 : upperElementarySubgroup (Fin 3) F) := by
          rw [hLeftCancel]

theorem bruhatMiddle_G01_s0
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) =
      fin3G01Monomial F := by
  have hFact := G01_S0_factorization_aux (F := F) a h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G01_s1
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) =
      fin3G01Monomial F := by
  have hFact := G01_S1_factorization_aux (F := F) a h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G01_s0
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) h12 = 1 := by
  have hFact := G01_S0_factorization_aux (F := F) a h01 h12
  have hNeg :
      (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G01Monomial_inv_perm]
    decide
  have hEntry :
      (((G01_L0Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 1) := by
    simp [G01_L0Fin3, G01_L1Fin3,
      UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply,
      Matrix.single_apply, Matrix.one_apply,
      Fin.sum_univ_three, Fin.isValue]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) h12
      = ((((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2)) := rfl
    _ = ((((G01_L0Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2)) := by
        rw [← hLeftEq]
    _ = 1 := hEntry

theorem leftSimpleRootCoeff_G01_s1
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) h12 = 0 := by
  have hFact := G01_S1_factorization_aux (F := F) a h01 h12
  have hNeg :
      (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G01Monomial_inv_perm]
    decide
  have hEntry :
      (((G01_L1Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
    simp [G01_L1Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply,
      Matrix.single_apply, Matrix.one_apply,
      Fin.isValue]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) h12
      = ((((Matrix.GeneralLinearGroup.bruhatLeft
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit
                  (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2)) := rfl
    _ = ((((G01_L1Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2)) := by
        rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_G01_s0_not_pos
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) ) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) ) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G01_s0 (F := F) a h01 h12
  rw [hMid, fin3G01Monomial_right_perm]
  decide

theorem bruhatMiddle_G01_s1_not_pos
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G01_s1 (F := F) a h01 h12
  rw [hMid, fin3G01Monomial_right_perm]
  decide

end G01TranslatedBruhat

section G10InversePrefixBruhat

variable {F : Type*} [Field F]

noncomputable def fin3G10InversePrefixMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)

theorem fin3G10InversePrefixMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3G10InversePrefixMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  unfold fin3G10InversePrefixMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

theorem fin3G10InversePrefixMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G10InversePrefixMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  have h := fin3G10InversePrefixMonomial_right_perm (F := F)
  have hInv :
      (fin3G10InversePrefixMonomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

private noncomputable def G10_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F)

private noncomputable def G10_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)

private noncomputable def G10_L1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (1 : F) *
    UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F)

private theorem G10_S0_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (_h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) =
    UpperElementary.toSLHom (G10_L0Fin3 F) *
      monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
      UpperElementary.toSLHom (G10_R0Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) := by
          unfold fin3G10InversePrefixMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (1 : F) := by
    unfold G10_L0Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10_R0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10_R0Fin3
    rw [toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (2 : Fin 3) ≠ 1) (-1 : F) := by
        rw [hWInv]
    _ = UpperElementary.toSLHom (G10_L0Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
          UpperElementary.toSLHom (G10_R0Fin3 F) := by
        rw [hL0, hR0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10_S1_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) =
    UpperElementary.toSLHom (G10_L1Fin3 F) *
      monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
      UpperElementary.toSLHom (G10_R0Fin3 F) := by
  have hS0 := G10_S0_factorization_aux (F := F) h01 h12
  have hTrans01 :
      Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F)) := by
    have hEq :
        UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (1 : F)) =
          Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (1 : F) := by
      rw [toSLHom_elementary_eq_transvection]
    calc Matrix.SpecialLinearGroup.transvection h01.ne (1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (1 : F) := by
          apply transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (1 : F)) := hEq.symm
  have hL0 :
      UpperElementary.toSLHom (G10_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (1 : F) := by
    unfold G10_L0Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hL1Mul :
      Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
        UpperElementary.toSLHom (G10_L0Fin3 F) =
        UpperElementary.toSLHom (G10_L1Fin3 F) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          UpperElementary.toSLHom (G10_L0Fin3 F)
        = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (1 : F)) *
            UpperElementary.toSLHom (G10_L0Fin3 F) := by
          rw [hTrans01]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (1 : F) * G10_L0Fin3 F) := by
          rw [← map_mul]
      _ = UpperElementary.toSLHom (G10_L1Fin3 F) := rfl
  calc Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))
      = Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          (UpperElementary.toSLHom (G10_L0Fin3 F) *
            monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
            UpperElementary.toSLHom (G10_R0Fin3 F)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          UpperElementary.toSLHom (G10_L0Fin3 F)) *
          monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
          UpperElementary.toSLHom (G10_R0Fin3 F) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10_L1Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G10InversePrefixMonomial F) *
          UpperElementary.toSLHom (G10_R0Fin3 F) := by
        rw [hL1Mul]

theorem bruhatMiddle_G10_inversePrefix_s0
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) =
      fin3G10InversePrefixMonomial F := by
  have hFact := G10_S0_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10_inversePrefix_s1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) =
      fin3G10InversePrefixMonomial F := by
  have hFact := G10_S1_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10_inversePrefix_s0
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) h01 = 0 := by
  have hFact := G10_S0_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3G10InversePrefixMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10InversePrefixMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10InversePrefixMonomial_inv_perm]
    decide
  have hEntry :
      (((G10_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    simp [G10_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((G10_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeftEq]
    _ = 0 := hEntry

theorem leftSimpleRootCoeff_G10_inversePrefix_s1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) h01 = 1 := by
  have hFact := G10_S1_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3G10InversePrefixMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10InversePrefixMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10InversePrefixMonomial_inv_perm]
    decide
  have hEntry :
      (((G10_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1 = 1) := by
    have hMul :
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F) *
          UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
            (by decide) (1 : F) =
          G10_L1Fin3 (F := F) := rfl
    rw [← hMul]
    have hCov := upperElementary_covBy_mul_entry
      (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (1 : F))
      (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F))
      h01
    rw [hCov]
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  let SL : Matrix.SpecialLinearGroup (Fin 3) F :=
    Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))
  have h1 : leftSimpleRootCoeff (F := F) (n := 3) (s := SL)
      h01 = ((Matrix.GeneralLinearGroup.bruhatLeft (SL :
          Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 := rfl
  have h2 : ((Matrix.GeneralLinearGroup.bruhatLeft (SL :
          Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 =
      ((G10_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 := by
    calc ((Matrix.GeneralLinearGroup.bruhatLeft (SL :
            Matrix.SpecialLinearGroup (Fin 3) F) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1
        = ((Matrix.GeneralLinearGroup.bruhatLeft
            (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit
                  (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) :
            Matrix.SpecialLinearGroup (Fin 3) F) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1 := by
          simp only [SL]
        _ = (((G10_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) 0 1) := by
          rw [← hLeftEq]
  calc leftSimpleRootCoeff (F := F) (n := 3) (s := SL) h01
      = ((Matrix.GeneralLinearGroup.bruhatLeft (SL :
          Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 := h1
    _ = ((G10_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 := h2
    _ = 1 := hEntry

theorem bruhatMiddle_G10_inversePrefix_s0_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10_inversePrefix_s0 (F := F) h01 h12
  rw [hMid, fin3G10InversePrefixMonomial_right_perm]
  decide

theorem bruhatMiddle_G10_inversePrefix_s1_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10_inversePrefix_s1 (F := F) h01 h12
  rw [hMid, fin3G10InversePrefixMonomial_right_perm]
  decide

end G10InversePrefixBruhat

section G10InverseStageThreeBruhat

variable {F : Type*} [Field F]

noncomputable def fin3G10InverseStageThreeMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
    (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)

theorem fin3G10InverseStageThreeMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3G10InverseStageThreeMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 2 := by
  unfold fin3G10InverseStageThreeMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

theorem fin3G10InverseStageThreeMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G10InverseStageThreeMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 2 := by
  have h := fin3G10InverseStageThreeMonomial_right_perm (F := F)
  have hInv :
      (fin3G10InverseStageThreeMonomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, Equiv.swap_inv]

private noncomputable def G10S3_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10S3_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F) *
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10S3_L1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private theorem G10S3_S0_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection
          h01.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection
          h12.ne.symm (-1 : F)) =
    UpperElementary.toSLHom (G10S3_L0Fin3 F) *
      monomialSLHom F (Fin 3)
        (fin3G10InverseStageThreeMonomial F) *
      UpperElementary.toSLHom (G10S3_R0Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply Subtype.ext
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe]
  have hT10 :
      Matrix.SpecialLinearGroup.transvection
          h01.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 0) (-1 : F) := by
    apply Subtype.ext
    rfl
  have hT21 :
      Matrix.SpecialLinearGroup.transvection
          h12.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (-1 : F) := by
    apply Subtype.ext
    rfl
  have hM :
      monomialSLHom F (Fin 3)
          (fin3G10InverseStageThreeMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
    have hEq :
        fin3G10InverseStageThreeMonomial (F := F) =
          Matrix.GeneralLinearGroup.weylMonomialSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := rfl
    calc monomialSLHom F (Fin 3)
            (fin3G10InverseStageThreeMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) := by
          rw [hEq]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10S3_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10S3_L0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10S3_R0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (-1 : F) := by
    unfold G10S3_R0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            h01.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            h12.ne.symm (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 0) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (-1 : F)) := by
          rw [hWInv, hT10, hT21]
    _ = UpperElementary.toSLHom (G10S3_L0Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10InverseStageThreeMonomial F) *
          UpperElementary.toSLHom (G10S3_R0Fin3 F) := by
        rw [hL0, hR0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10S3_L_mul
    (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 3) ≠ 2) (-1 : F) *
      UpperElementary.toSLHom (G10S3_L0Fin3 F) =
    UpperElementary.toSLHom (G10S3_L1Fin3 F) := by
  have hL0 :
      UpperElementary.toSLHom (G10S3_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10S3_L0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hL1 :
      UpperElementary.toSLHom (G10S3_L1Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10S3_L1Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  rw [hL0, hL1]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]

private theorem G10S3_S1_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            h01.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            h12.ne.symm (-1 : F))) =
    UpperElementary.toSLHom (G10S3_L1Fin3 F) *
      monomialSLHom F (Fin 3)
        (fin3G10InverseStageThreeMonomial F) *
      UpperElementary.toSLHom (G10S3_R0Fin3 F) := by
  have hS0 := G10S3_S0_factorization_aux (F := F) h01 h12
  have hT12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    apply Subtype.ext
    rfl
  have hLmul := G10S3_L_mul (F := F)
  calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) *
          (UpperElementary.toSLHom (G10S3_L0Fin3 F) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageThreeMonomial F) *
            UpperElementary.toSLHom (G10S3_R0Fin3 F)) := by
          rw [hS0, hT12]
    _ = (Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) *
          UpperElementary.toSLHom (G10S3_L0Fin3 F)) *
          monomialSLHom F (Fin 3)
            (fin3G10InverseStageThreeMonomial F) *
          UpperElementary.toSLHom (G10S3_R0Fin3 F) := by
          simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10S3_L1Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10InverseStageThreeMonomial F) *
          UpperElementary.toSLHom (G10S3_R0Fin3 F) := by
          rw [hLmul]

theorem bruhatMiddle_G10InverseStageThree_weyl12_inv_mul_T10_T21
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F))) =
      fin3G10InverseStageThreeMonomial F := by
  have hFact := G10S3_S0_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10InverseStageThree_T12_weyl12_inv_T10_T21
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F)))) =
      fin3G10InverseStageThreeMonomial F := by
  have hFact := G10S3_S1_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10InverseStageThree_weyl12_inv_T10_T21
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F))) h12 = 0 := by
  have hFact := G10S3_S0_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3G10InverseStageThreeMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10InverseStageThreeMonomial F :
            MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10InverseStageThreeMonomial_inv_perm]
    decide
  have hEntry :
      (((G10S3_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
    simp [G10S3_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.single_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.add_apply, Fin.isValue]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  h01.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  h12.ne.symm (-1 : F))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((G10S3_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := by
          rw [← hLeftEq]
    _ = 0 := hEntry

theorem leftSimpleRootCoeff_G10InverseStageThree_T12_weyl12_T10_T21
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F)))) h12 = -1 := by
  have hFact := G10S3_S1_factorization_aux (F := F) h01 h12
  have hNeg :
      (fin3G10InverseStageThreeMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10InverseStageThreeMonomial F :
            MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10InverseStageThreeMonomial_inv_perm]
    decide
  have hEntry :
      (((G10S3_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2 = -1) := by
    simp [G10S3_L1Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.single_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.add_apply, Fin.isValue]
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F)))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit
                  (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    h01.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    h12.ne.symm (-1 : F)))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((G10S3_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2) := by
          rw [← hLeftEq]
    _ = -1 := hEntry

theorem bruhatMiddle_G10InverseStageThree_weyl12_T10_T21_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              h12.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_G10InverseStageThree_weyl12_inv_mul_T10_T21
      (F := F) h01 h12
  rw [hMid, fin3G10InverseStageThreeMonomial_right_perm]
  decide

theorem bruhatMiddle_G10InverseStageThree_T12_weyl12_T10_T21_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                h12.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_G10InverseStageThree_T12_weyl12_inv_T10_T21
      (F := F) h01 h12
  rw [hMid, fin3G10InverseStageThreeMonomial_right_perm]
  decide

end G10InverseStageThreeBruhat

section G10InverseStageFourBruhat

variable {F : Type*} [Field F]

/-- Shared monomial for G10 inverse Stage 4:
`M4 = w₁₂(1) * w₀₁(-1)` over `Fin 3`. Permutation is
`swap 1 2 * swap 0 1` with inverse `swap 0 1 * swap 1 2`. -/
noncomputable def fin3G10InverseStageFourMonomial
    (F : Type*) [Field F] : MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)

private theorem fin3G10InverseStageFourMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3G10InverseStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  unfold fin3G10InverseStageFourMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10InverseStageFourMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G10InverseStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  have h := fin3G10InverseStageFourMonomial_right_perm (F := F)
  have hInv :
      (fin3G10InverseStageFourMonomial (F := F) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)⁻¹ := by
    rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

theorem fin3G10InverseStageFourMonomial_right
    (F : Type*) [Field F] :
    (fin3G10InverseStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 :=
  fin3G10InverseStageFourMonomial_right_perm F

theorem fin3G10InverseStageFourMonomial_inv
    (F : Type*) [Field F] :
    (fin3G10InverseStageFourMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 :=
  fin3G10InverseStageFourMonomial_inv_perm F

private noncomputable def G10S4_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10S4_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10S4_L1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private theorem G10S4_weyl_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem G10S4_transvection_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
      Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

private theorem G10S4_S0_factorization_aux
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
        Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F)) =
    UpperElementary.toSLHom (G10S4_L0Fin3 F) *
      monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
      UpperElementary.toSLHom (G10S4_R0Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hWInv' :
      Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) :=
    G10S4_weyl_ne_irrel h01.ne _ _
  have hM :
      monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) := by
          unfold fin3G10InverseStageFourMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hT21_1 :
      Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (1 : F) :=
    G10S4_transvection_ne_irrel h12.ne.symm _ _
  have hT10_neg :
      Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 0) (-1 : F) :=
    G10S4_transvection_ne_irrel h01.ne.symm _ _
  have hT21_neg :
      Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (2 : Fin 3) ≠ 1) (-1 : F) :=
    G10S4_transvection_ne_irrel h12.ne.symm _ _
  have hL0 :
      UpperElementary.toSLHom (G10S4_L0Fin3 F) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10S4_L0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10S4_R0Fin3 F) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10S4_R0Fin3
    rw [toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 0) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 1) (-1 : F)) := by
        rw [hWInv, hWInv', hT21_1, hT10_neg, hT21_neg]
    _ = UpperElementary.toSLHom (G10S4_L0Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
          UpperElementary.toSLHom (G10S4_R0Fin3 F) := by
        rw [hL0, hR0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10S4_S1_factorization_aux_correct
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F))) =
    UpperElementary.toSLHom (G10S4_L1Fin3 F) *
      monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
      UpperElementary.toSLHom (G10S4_R0Fin3 F) := by
  have hS0 := G10S4_S0_factorization_aux (F := F) h01 h12
  have hTrans01 :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (-1 : F) := by
          apply G10S4_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hL0_eq :
      G10S4_L0Fin3 (F := F) =
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F) *
          G10S4_L1Fin3 F := rfl
  have hCancel :
      UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
          (by decide) (-1 : F) *
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
          (by decide) (1 : F) = 1 := by
    have hAdd :
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) *
          UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F) =
          UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) ((-1 : F) + 1) := by
      apply Subtype.ext
      simp [Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hAdd]
    have hZero : ((-1 : F) + 1) = 0 := by simp
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one h01
  have hLeftCancel :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        UpperElementary.toSLHom (G10S4_L0Fin3 F) =
        UpperElementary.toSLHom (G10S4_L1Fin3 F) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          UpperElementary.toSLHom (G10S4_L0Fin3 F)
        = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) *
            UpperElementary.toSLHom (G10S4_L0Fin3 F) := by
          rw [hTrans01]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) * G10S4_L0Fin3 F) := by
          rw [← map_mul]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) *
                (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                  (by decide) (1 : F) *
                G10S4_L1Fin3 F)) := by
          rw [hL0_eq]
      _ = UpperElementary.toSLHom
              ((UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) *
              UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (1 : F)) *
            G10S4_L1Fin3 F) := by
          rw [mul_assoc]
      _ = UpperElementary.toSLHom
              (1 * G10S4_L1Fin3 F) := by
          rw [hCancel]
      _ = UpperElementary.toSLHom (G10S4_L1Fin3 F) := by
          simp
  calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (UpperElementary.toSLHom (G10S4_L0Fin3 F) *
            monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10S4_R0Fin3 F)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          UpperElementary.toSLHom (G10S4_L0Fin3 F)) *
          monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
          UpperElementary.toSLHom (G10S4_R0Fin3 F) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10S4_L1Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G10InverseStageFourMonomial F) *
          UpperElementary.toSLHom (G10S4_R0Fin3 F) := by
        rw [hLeftCancel]

theorem bruhatMiddle_G10InverseStageFour_D0
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F))) =
      fin3G10InverseStageFourMonomial F := by
  have hFact := G10S4_S0_factorization_aux (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10InverseStageFour_D1
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F)))) =
      fin3G10InverseStageFourMonomial F := by
  have hFact := G10S4_S1_factorization_aux_correct (F := F) h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10InverseStageFour_D0_pos
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) := by
  have hMid := bruhatMiddle_G10InverseStageFour_D0 (F := F) h01 h12
  rw [hMid, fin3G10InverseStageFourMonomial_right_perm]
  decide

theorem bruhatMiddle_G10InverseStageFour_D1_pos
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection h01.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection h12.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) := by
  have hMid := bruhatMiddle_G10InverseStageFour_D1 (F := F) h01 h12
  rw [hMid, fin3G10InverseStageFourMonomial_right_perm]
  decide

end G10InverseStageFourBruhat

section G10TranslatedStageOneBruhat

variable {F : Type*} [Field F]

private theorem G10Trans1_weyl_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem G10Trans1_transvection_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
      Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

private noncomputable def G10Trans1_L0Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) a *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10Trans1_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10Trans1_L1Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (1 : F) *
    G10Trans1_L0Fin3 F a

private theorem G10Trans1_S0_factorization_aux
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) =
    UpperElementary.toSLHom (G10Trans1_L0Fin3 F a) *
      monomialSLHom F (Fin 3)
        (fin3G10InverseStageFourMonomial F) *
      UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hWInv' :
      Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) :=
    G10Trans1_weyl_ne_irrel h01.ne _ _
  have hM :
      monomialSLHom F (Fin 3)
          (fin3G10InverseStageFourMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10InverseStageFourMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) := by
          unfold fin3G10InverseStageFourMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hT12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-a) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (-a) :=
    G10Trans1_transvection_ne_irrel h12.ne _ _
  have hL0 :
      UpperElementary.toSLHom (G10Trans1_L0Fin3 F a) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) a *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans1_L0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10Trans1_R0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans1_R0Fin3
    rw [toSLHom_elementary_eq_transvection]
  calc (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 2) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (2 : Fin 3) ≠ 0) (-1 : F)) := by
          rw [hWInv, hWInv', hT12]
      _ = UpperElementary.toSLHom (G10Trans1_L0Fin3 F a) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
          rw [hL0, hR0, hM]
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.weylSLUnit,
              Matrix.SpecialLinearGroup.transvection_coe,
              Matrix.SpecialLinearGroup.coe_mul,
              Matrix.add_apply, Matrix.single_apply,
              Matrix.one_apply, Matrix.mul_apply,
              Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans1_S1_factorization_aux
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
    UpperElementary.toSLHom (G10Trans1_L1Fin3 F a) *
      monomialSLHom F (Fin 3)
        (fin3G10InverseStageFourMonomial F) *
      UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
  have hS0 :=
    G10Trans1_S0_factorization_aux (F := F) a h01 h12
  have hTrans01 :
      Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (1 : F) := by
          apply G10Trans1_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hL1 :
      UpperElementary.toSLHom (G10Trans1_L1Fin3 F a) =
        UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (1 : F)) *
          UpperElementary.toSLHom (G10Trans1_L0Fin3 F a) := by
    unfold G10Trans1_L1Fin3
    rw [map_mul]
  calc Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))
      = Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          (UpperElementary.toSLHom (G10Trans1_L0Fin3 F a) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10Trans1_R0Fin3 F)) := by
          rw [hS0]
      _ = (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
            UpperElementary.toSLHom (G10Trans1_L0Fin3 F a)) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
          simp only [mul_assoc]
      _ = (UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (1 : F)) *
            UpperElementary.toSLHom (G10Trans1_L0Fin3 F a)) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
          rw [hTrans01]
      _ = UpperElementary.toSLHom (G10Trans1_L1Fin3 F a) *
            monomialSLHom F (Fin 3)
              (fin3G10InverseStageFourMonomial F) *
            UpperElementary.toSLHom (G10Trans1_R0Fin3 F) := by
          rw [← hL1]

theorem bruhatMiddle_G10TranslatedStageOne_C0
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
      fin3G10InverseStageFourMonomial F := by
  have hFact :=
    G10Trans1_S0_factorization_aux (F := F) a h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageOne_C1
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      fin3G10InverseStageFourMonomial F := by
  have hFact :=
    G10Trans1_S1_factorization_aux (F := F) a h01 h12
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageOne_C0_pos
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) ) :
        MonomialBase Fˣ (Fin 3)).right.symm 0 <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) ) :
        MonomialBase Fˣ (Fin 3)).right.symm 1 := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageOne_C0 (F := F) a h01 h12
  rw [hMid, fin3G10InverseStageFourMonomial_right]
  decide

theorem bruhatMiddle_G10TranslatedStageOne_C1_pos
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm 0 <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection h12.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm 1 := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageOne_C1 (F := F) a h01 h12
  rw [hMid, fin3G10InverseStageFourMonomial_right]
  decide

end G10TranslatedStageOneBruhat

section G10TranslatedStageTwoBruhat

variable {F : Type*} [Field F]

private theorem G10Trans2_weyl_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem G10Trans2_transvection_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
      Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

noncomputable def fin3G10TranslatedStageTwoGenericMonomial
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1) :
    MonomialSL F (Fin 3) :=
  let hOneSub : (1 : F) - a ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm ha)
  Matrix.GeneralLinearGroup.torusMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide)
      ((Units.mk0 (1 - a) hOneSub)⁻¹) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)

noncomputable def fin3G10TranslatedStageTwoExceptionalMonomial
    (F : Type*) [Field F] :
    MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)

private theorem fin3G10Trans2GenericMonomial_right_perm
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1) :
    (fin3G10TranslatedStageTwoGenericMonomial F a ha :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 2 := by
  unfold fin3G10TranslatedStageTwoGenericMonomial
  simp [Matrix.GeneralLinearGroup.torusMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.torusPerm,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10Trans2GenericMonomial_inv_perm
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1) :
    (fin3G10TranslatedStageTwoGenericMonomial F a ha :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 2 := by
  have h := fin3G10Trans2GenericMonomial_right_perm
    (F := F) (a := a) (ha := ha)
  have hInv :
      (fin3G10TranslatedStageTwoGenericMonomial F a ha :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 2)⁻¹ := by rw [h]
  rw [hInv, Equiv.swap_inv]





private theorem fin3G10Trans2ExceptionalMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3G10TranslatedStageTwoExceptionalMonomial F :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  unfold fin3G10TranslatedStageTwoExceptionalMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10Trans2ExceptionalMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G10TranslatedStageTwoExceptionalMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  have h := fin3G10Trans2ExceptionalMonomial_right_perm (F := F)
  have hInv :
      (fin3G10TranslatedStageTwoExceptionalMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]





private noncomputable def G10Trans2_P2Fin3
    (F : Type*) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 2 by decide) (-a) *
      Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))

private noncomputable def G10Trans2_C0Fin3
    (F : Type*) [Field F] (a : F)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit
      (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
    G10Trans2_P2Fin3 F a

private noncomputable def G10Trans2_C1Fin3
    (F : Type*) [Field F] (a : F)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
    G10Trans2_C0Fin3 F a h12

private noncomputable def G10Trans2_L0Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) ((a - 1)⁻¹)

private noncomputable def G10Trans2_R0Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) ((a - 1)⁻¹) *
    (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
        (by decide) (-1 : F) *
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) (-1 : F))

private noncomputable def G10Trans2_L1Fin3
    (F : Type*) [Field F] (a : F) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F) *
    G10Trans2_L0Fin3 F a

private noncomputable def G10Trans2e_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
    (by decide) (1 : F)

private noncomputable def G10Trans2e_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10Trans2e_L1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F) *
    G10Trans2e_L0Fin3 F

private theorem G10Trans2_S0_factorization_aux
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans2_C0Fin3 F a h12 =
      UpperElementary.toSLHom (G10Trans2_L0Fin3 F a) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
        UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) := by
  have hOneSub : (1 : F) - a ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm ha)
  have hSub : a - 1 ≠ 0 :=
    sub_ne_zero.mpr ha
  have hOneSub_mk :
      (Units.mk0 (1 - a) hOneSub : F) = 1 - a := by
    simp [Units.val_mk0]
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans2_weyl_ne_irrel
  have hM_eq :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoGenericMonomial F a ha) =
        Matrix.GeneralLinearGroup.torusSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide)
            ((Units.mk0 (1 - a) hOneSub)⁻¹) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoGenericMonomial F a ha)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.torusMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide)
              ((Units.mk0 (1 - a) hOneSub)⁻¹)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) := by
          unfold fin3G10TranslatedStageTwoGenericMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.torusSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide)
              ((Units.mk0 (1 - a) hOneSub)⁻¹) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10Trans2_L0Fin3 F a) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) ((a - 1)⁻¹) := by
    unfold G10Trans2_L0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) ((a - 1)⁻¹) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 2) (-1 : F)) := by
    unfold G10Trans2_R0Fin3
    rw [map_mul, map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc G10Trans2_C0Fin3 F a h12
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
        unfold G10Trans2_C0Fin3 G10Trans2_P2Fin3
        rw [hWInv]
    _ = UpperElementary.toSLHom (G10Trans2_L0Fin3 F a) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
          UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) := by
        rw [hL0, hR0, hM_eq,
          Matrix.GeneralLinearGroup.torusSLUnit_eq_diag2n]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.diag2n_coe,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue,
            Units.val_mk0,
            Matrix.diagonal_apply] <;>
          field_simp <;>
          ring

private theorem G10Trans2_S1_factorization_aux
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans2_C1Fin3 F a h12 =
      UpperElementary.toSLHom (G10Trans2_L1Fin3 F a) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
        UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) := by
  have hS0 := G10Trans2_S0_factorization_aux (F := F) a ha h12
  have hT12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (1 : Fin 3) < 2)) (1 : F) := by
          apply G10Trans2_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  calc G10Trans2_C1Fin3 F a h12
      = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          G10Trans2_C0Fin3 F a h12 := rfl
    _ = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          (UpperElementary.toSLHom (G10Trans2_L0Fin3 F a) *
            monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
            UpperElementary.toSLHom (G10Trans2_R0Fin3 F a)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          UpperElementary.toSLHom (G10Trans2_L0Fin3 F a)) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
          UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10Trans2_L1Fin3 F a) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoGenericMonomial F a ha) *
          UpperElementary.toSLHom (G10Trans2_R0Fin3 F a) := by
        have : Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
            UpperElementary.toSLHom (G10Trans2_L0Fin3 F a) =
            UpperElementary.toSLHom (G10Trans2_L1Fin3 F a) := by
          rw [hT12, ← map_mul]
          rfl
        rw [this]

private theorem G10Trans2e_S0_factorization_aux
    (F : Type*) [Field F]
    (_h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans2_C0Fin3 F 1 h12 =
      UpperElementary.toSLHom (G10Trans2e_L0Fin3 F) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoExceptionalMonomial F) *
        UpperElementary.toSLHom (G10Trans2e_R0Fin3 F) := by
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans2_weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoExceptionalMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoExceptionalMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)) := by
          unfold fin3G10TranslatedStageTwoExceptionalMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10Trans2e_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 1) (1 : F) := by
    unfold G10Trans2e_L0Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10Trans2e_R0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans2e_R0Fin3
    rw [map_mul, toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc G10Trans2_C0Fin3 F 1 h12
      = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
        unfold G10Trans2_C0Fin3 G10Trans2_P2Fin3
        rw [hWInv]
    _ = UpperElementary.toSLHom (G10Trans2e_L0Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoExceptionalMonomial F) *
          UpperElementary.toSLHom (G10Trans2e_R0Fin3 F) := by
        rw [hL0, hR0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans2e_S1_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans2_C1Fin3 F 1 h12 =
      UpperElementary.toSLHom (G10Trans2e_L1Fin3 F) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageTwoExceptionalMonomial F) *
        UpperElementary.toSLHom (G10Trans2e_R0Fin3 F) := by
  have hS0 := G10Trans2e_S0_factorization_aux (F := F) h01 h12
  have hT12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (1 : Fin 3) < 2)) (1 : F) := by
          apply G10Trans2_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  calc G10Trans2_C1Fin3 F 1 h12
      = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          G10Trans2_C0Fin3 F 1 h12 := rfl
    _ = Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          (UpperElementary.toSLHom (G10Trans2e_L0Fin3 F) *
            monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageTwoExceptionalMonomial F) *
            UpperElementary.toSLHom (G10Trans2e_R0Fin3 F)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          UpperElementary.toSLHom (G10Trans2e_L0Fin3 F)) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoExceptionalMonomial F) *
          UpperElementary.toSLHom (G10Trans2e_R0Fin3 F) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10Trans2e_L1Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageTwoExceptionalMonomial F) *
          UpperElementary.toSLHom (G10Trans2e_R0Fin3 F) := by
        have : Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
            UpperElementary.toSLHom (G10Trans2e_L0Fin3 F) =
            UpperElementary.toSLHom (G10Trans2e_L1Fin3 F) := by
          rw [hT12, ← map_mul]
          rfl
        rw [this]

theorem bruhatMiddle_G10TranslatedStageTwo_C0
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      fin3G10TranslatedStageTwoGenericMonomial F a ha := by
  have hFact := G10Trans2_S0_factorization_aux F a ha h12
  have hEq : (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        G10Trans2_C0Fin3 F a h12 := by
    unfold G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageTwo_C1
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      fin3G10TranslatedStageTwoGenericMonomial F a ha := by
  have hFact := G10Trans2_S1_factorization_aux F a ha h12
  have hEq : Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
        G10Trans2_C1Fin3 F a h12 := by
    unfold G10Trans2_C1Fin3 G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10TranslatedStageTwo_C0
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) h12 =
      (a - 1)⁻¹ := by
  have hFact := G10Trans2_S0_factorization_aux F a ha h12
  have hNeg :
      (fin3G10TranslatedStageTwoGenericMonomial F a ha :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10TranslatedStageTwoGenericMonomial F a ha :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10Trans2GenericMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans2_L0Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = (a - 1)⁻¹) := by
    simp [G10Trans2_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.isValue]
  have hEqC0 : (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        G10Trans2_C0Fin3 F a h12 := by
    unfold G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hBL : Matrix.GeneralLinearGroup.bruhatLeft
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans2_C0Fin3 F a h12) := by
    rw [hEqC0]
  calc leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans2_C0Fin3 F a h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := by
        rw [hBL]
    _ = (((G10Trans2_L0Fin3 F a :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2) := by
        rw [← hLeftEq]
    _ = (a - 1)⁻¹ := hEntry

theorem leftSimpleRootCoeff_G10TranslatedStageTwo_C1
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h12 =
      a / (a - 1) := by
  have hFact := G10Trans2_S1_factorization_aux F a ha h12
  have hNeg :
      (fin3G10TranslatedStageTwoGenericMonomial F a ha :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10TranslatedStageTwoGenericMonomial F a ha :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10Trans2GenericMonomial_inv_perm]
    decide
  have hSub : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hRaw :
      (((G10Trans2_L1Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = (a - 1)⁻¹ + 1) := by
    simp [G10Trans2_L1Fin3, G10Trans2_L0Fin3,
      UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.sum_univ_three, Fin.isValue]
  have hEq : (a - 1)⁻¹ + 1 = a / (a - 1) := by
    have : a - 1 ≠ 0 := hSub
    field_simp
    ring
  have hEntry :
      (((G10Trans2_L1Fin3 F a :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = a / (a - 1)) := by
    calc (((G10Trans2_L1Fin3 F a :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 1 2)
        = (a - 1)⁻¹ + 1 := hRaw
      _ = a / (a - 1) := hEq
  have hEqC1 : Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
        G10Trans2_C1Fin3 F a h12 := by
    unfold G10Trans2_C1Fin3 G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hBL : Matrix.GeneralLinearGroup.bruhatLeft
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans2_C1Fin3 F a h12) := by
    rw [hEqC1]
  calc leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans2_C1Fin3 F a h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := by
        rw [hBL]
    _ = (((G10Trans2_L1Fin3 F a :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2) := by
        rw [← hLeftEq]
    _ = a / (a - 1) := hEntry

theorem bruhatMiddle_G10TranslatedStageTwo_C0_not_pos
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageTwo_C0 F a ha h12
  rw [hMid, fin3G10Trans2GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageTwo_C1_not_pos
    (F : Type*) [Field F] (a : F) (ha : a ≠ 1)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) ) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) ) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageTwo_C1 F a ha h12
  rw [hMid, fin3G10Trans2GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageTwo_exceptional_C0
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      fin3G10TranslatedStageTwoExceptionalMonomial F := by
  have hFact := G10Trans2e_S0_factorization_aux (F := F) h01 h12
  have hEq : (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        G10Trans2_C0Fin3 F 1 h12 := by
    unfold G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageTwo_exceptional_C1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      fin3G10TranslatedStageTwoExceptionalMonomial F := by
  have hFact := G10Trans2e_S1_factorization_aux (F := F) h01 h12
  have hEq : Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
        G10Trans2_C1Fin3 F 1 h12 := by
    unfold G10Trans2_C1Fin3 G10Trans2_C0Fin3 G10Trans2_P2Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageTwo_exceptional_C0_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageTwo_exceptional_C0 F h01 h12
  rw [hMid, fin3G10Trans2ExceptionalMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageTwo_exceptional_C1_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3))
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(1 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) := by
  have hMid :=
    bruhatMiddle_G10TranslatedStageTwo_exceptional_C1 F h01 h12
  rw [hMid, fin3G10Trans2ExceptionalMonomial_right_perm]
  decide

end G10TranslatedStageTwoBruhat

section G10TranslatedStageThreeBruhat

variable {F : Type*} [Field F]

private theorem G10Trans3_weyl_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem G10Trans3_transvection_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
      Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

noncomputable def fin3G10TranslatedStageThreeGenericMonomial
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    MonomialSL F (Fin 3) :=
  let haInv : a⁻¹ ≠ 0 := inv_ne_zero ha0
  let hNegInv : -a⁻¹ ≠ 0 := neg_ne_zero.mpr haInv
  Matrix.GeneralLinearGroup.torusMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide)
      (Units.mk0 (-a⁻¹) hNegInv) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)

noncomputable def fin3G10TranslatedStageThreeZeroMonomial
    (F : Type*) [Field F] :
    MonomialSL F (Fin 3) :=
  Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)

private theorem fin3G10Trans3GenericMonomial_right_perm
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
      MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 2 := by
  unfold fin3G10TranslatedStageThreeGenericMonomial
  simp [Matrix.GeneralLinearGroup.torusMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.torusPerm,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10Trans3GenericMonomial_inv_perm
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
      MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 2 := by
  have h := fin3G10Trans3GenericMonomial_right_perm
    (F := F) (a := a) (ha0 := ha0)
  have hInv :
      (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 2)⁻¹ := by rw [h]
  rw [hInv, Equiv.swap_inv]

private theorem fin3G10Trans3ZeroMonomial_right_perm
    (F : Type*) [Field F] :
    (fin3G10TranslatedStageThreeZeroMonomial F :
      MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  unfold fin3G10TranslatedStageThreeZeroMonomial
  simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10Trans3ZeroMonomial_inv_perm
    (F : Type*) [Field F] :
    (fin3G10TranslatedStageThreeZeroMonomial F :
      MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  have h := fin3G10Trans3ZeroMonomial_right_perm (F := F)
  have hInv :
      (fin3G10TranslatedStageThreeZeroMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)⁻¹ := by
    rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

private noncomputable def G10Trans3_P3Fin3
    (F : Type*) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
      (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))

private noncomputable def G10Trans3_C0Fin3
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
    G10Trans3_P3Fin3 F a

private noncomputable def G10Trans3_C1Fin3
    (F : Type*) [Field F] (a : F)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
    G10Trans3_C0Fin3 F a h01

private noncomputable def G10Trans3_Gen_L0Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (1 : F) *
    (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-a⁻¹))

private noncomputable def G10Trans3_Gen_R0Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (a⁻¹) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-(1 + a))

private noncomputable def G10Trans3_Gen_L1Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-a⁻¹)

private noncomputable def G10Trans3_ZeroP3Fin3
    (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
      Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))

private noncomputable def G10Trans3_ZeroC0Fin3
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
    G10Trans3_ZeroP3Fin3 F

private noncomputable def G10Trans3_ZeroC1Fin3
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
    G10Trans3_ZeroC0Fin3 F h01

private noncomputable def G10Trans3_Zero_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (1 : F) *
    (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F) *
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F))

private noncomputable def G10Trans3_Zero_R0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : F) *
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)

private noncomputable def G10Trans3_Zero_L1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3) (by decide) (1 : F)

private noncomputable def G10Trans3_Zero_R1Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : F)

private theorem G10Trans3_gen_S0_factorization_aux
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    G10Trans3_C0Fin3 F a h01 =
      UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) := by
  have haInv : a⁻¹ ≠ 0 := inv_ne_zero ha0
  have hNegInv : -a⁻¹ ≠ 0 := neg_ne_zero.mpr haInv
  have hWInv01 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans3_weyl_ne_irrel
  have hM_eq :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeGenericMonomial F a ha0) =
        Matrix.GeneralLinearGroup.torusSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide)
          (Units.mk0 (-a⁻¹) hNegInv) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeGenericMonomial F a ha0)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.torusMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide)
              (Units.mk0 (-a⁻¹) hNegInv)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)) := by
          unfold fin3G10TranslatedStageThreeGenericMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.torusSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (Units.mk0 (-a⁻¹) hNegInv) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 2) (-a⁻¹)) := by
    unfold G10Trans3_Gen_L0Fin3
    rw [map_mul, map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (a⁻¹) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-(1 + a)) := by
    unfold G10Trans3_Gen_R0Fin3
    rw [map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc G10Trans3_C0Fin3 F a h01
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          G10Trans3_P3Fin3 F a := by
        unfold G10Trans3_C0Fin3 G10Trans3_P3Fin3
        rw [hWInv01]
    _ = UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) := by
        rw [hL0, hR0, hM_eq,
          Matrix.GeneralLinearGroup.torusSLUnit_eq_diag2n]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.diag2n_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue,
            Units.val_mk0, Matrix.diagonal_apply,
            G10Trans3_P3Fin3] <;>
          field_simp <;>
          ring

private theorem G10Trans3_gen_S1_factorization_aux
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    G10Trans3_C1Fin3 F a h01 =
      UpperElementary.toSLHom (G10Trans3_Gen_L1Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) := by
  have hS0 := G10Trans3_gen_S0_factorization_aux (F := F) a ha0 h01
  have hTrans01 :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (-1 : F) := by
          apply G10Trans3_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hL0_eq :
      G10Trans3_Gen_L0Fin3 (F := F) a ha0 =
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F) *
          G10Trans3_Gen_L1Fin3 F a ha0 := rfl
  have hCancel :
      UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
          (by decide) (-1 : F) *
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
          (by decide) (1 : F) = 1 := by
    have hAdd :
        UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (-1 : F) *
          UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) (1 : F) =
          UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
            (by decide) ((-1 : F) + 1) := by
      apply Subtype.ext
      simp [Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hAdd]
    have hZero : ((-1 : F) + 1) = 0 := by simp
    rw [hZero]
    exact upperElementary_elementary_zero_eq_one h01
  have hLeftCancel :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) =
        UpperElementary.toSLHom (G10Trans3_Gen_L1Fin3 F a ha0) := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0)
        = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) *
            UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) := by
          rw [hTrans01]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) * G10Trans3_Gen_L0Fin3 F a ha0) := by
          rw [← map_mul]
      _ = UpperElementary.toSLHom
              (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) *
                (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                  (by decide) (1 : F) *
                G10Trans3_Gen_L1Fin3 F a ha0)) := by
          rw [hL0_eq]
      _ = UpperElementary.toSLHom
              ((UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F) *
              UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (1 : F)) *
            G10Trans3_Gen_L1Fin3 F a ha0) := by
          rw [mul_assoc]
      _ = UpperElementary.toSLHom
              (1 * G10Trans3_Gen_L1Fin3 F a ha0) := by
          rw [hCancel]
      _ = UpperElementary.toSLHom (G10Trans3_Gen_L1Fin3 F a ha0) := by
          simp
  calc G10Trans3_C1Fin3 F a h01
      = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          G10Trans3_C0Fin3 F a h01 := rfl
    _ = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0) *
            monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
            UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          UpperElementary.toSLHom (G10Trans3_Gen_L0Fin3 F a ha0)) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10Trans3_Gen_L1Fin3 F a ha0) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans3_Gen_R0Fin3 F a ha0) := by
        rw [hLeftCancel]

private theorem G10Trans3_zero_S0_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    G10Trans3_ZeroC0Fin3 F h01 =
      UpperElementary.toSLHom (G10Trans3_Zero_L0Fin3 F) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeZeroMonomial F) *
        UpperElementary.toSLHom (G10Trans3_Zero_R0Fin3 F) := by
  have hWInv01 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans3_weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeZeroMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeZeroMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) := by
          unfold fin3G10TranslatedStageThreeZeroMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL0 :
      UpperElementary.toSLHom (G10Trans3_Zero_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (1 : Fin 3) ≠ 2) (-1 : F)) := by
    unfold G10Trans3_Zero_L0Fin3
    rw [map_mul, map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  have hR0 :
      UpperElementary.toSLHom (G10Trans3_Zero_R0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans3_Zero_R0Fin3
    rw [map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc G10Trans3_ZeroC0Fin3 F h01
      = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          G10Trans3_ZeroP3Fin3 F := by
        unfold G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
        rw [hWInv01]
    _ = UpperElementary.toSLHom (G10Trans3_Zero_L0Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeZeroMonomial F) *
          UpperElementary.toSLHom (G10Trans3_Zero_R0Fin3 F) := by
        rw [hL0, hR0, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue,
            G10Trans3_ZeroP3Fin3]

private theorem G10Trans3_zero_S1_factorization_aux
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    G10Trans3_ZeroC1Fin3 F h01 =
      UpperElementary.toSLHom (G10Trans3_Zero_L1Fin3 F) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeZeroMonomial F) *
        UpperElementary.toSLHom (G10Trans3_Zero_R1Fin3 F) := by
  have hWInv01 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans3_weyl_ne_irrel
  have hM :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageThreeZeroMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeZeroMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) := by
          unfold fin3G10TranslatedStageThreeZeroMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hL1 :
      UpperElementary.toSLHom (G10Trans3_Zero_L1Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (0 : Fin 3) ≠ 2) (1 : F) := by
    unfold G10Trans3_Zero_L1Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hR1 :
      UpperElementary.toSLHom (G10Trans3_Zero_R1Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans3_Zero_R1Fin3
    rw [toSLHom_elementary_eq_transvection]
  have hT01 : Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
      Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) (-1 : F) := by
    apply G10Trans3_transvection_ne_irrel
  calc G10Trans3_ZeroC1Fin3 F h01
      = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        G10Trans3_ZeroC0Fin3 F h01 := rfl
    _ = Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) *
            G10Trans3_ZeroP3Fin3 F) := by
        rw [hT01]
        unfold G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
        rw [hWInv01]
    _ = UpperElementary.toSLHom (G10Trans3_Zero_L1Fin3 F) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageThreeZeroMonomial F) *
          UpperElementary.toSLHom (G10Trans3_Zero_R1Fin3 F) := by
        rw [hL1, hR1, hM]
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.GeneralLinearGroup.weylSLUnit,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue,
            G10Trans3_ZeroP3Fin3]

theorem bruhatMiddle_G10TranslatedStageThree_C0
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      fin3G10TranslatedStageThreeGenericMonomial F a ha0 := by
  have hFact := G10Trans3_gen_S0_factorization_aux F a ha0 h01
  have hEq :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans3_C0Fin3 F a h01 := by
    unfold G10Trans3_C0Fin3 G10Trans3_P3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageThree_C1
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      fin3G10TranslatedStageThreeGenericMonomial F a ha0 := by
  have hFact := G10Trans3_gen_S1_factorization_aux F a ha0 h01
  have hEq :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans3_C1Fin3 F a h01 := by
    unfold G10Trans3_C1Fin3 G10Trans3_C0Fin3 G10Trans3_P3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10TranslatedStageThree_C0
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h01 =
      1 := by
  have hFact := G10Trans3_gen_S0_factorization_aux F a ha0 h01
  have hNeg :
      (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10Trans3GenericMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans3_Gen_L0Fin3 F a ha0 :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 1) := by
    simp [G10Trans3_Gen_L0Fin3,
      UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.isValue]
  have hEqC0 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans3_C0Fin3 F a h01 := by
    unfold G10Trans3_C0Fin3 G10Trans3_P3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      Matrix.GeneralLinearGroup.bruhatLeft (G10Trans3_C0Fin3 F a h01) := by
    rw [hEqC0]
  calc leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans3_C0Fin3 F a h01) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by rw [hBL]
    _ = (((G10Trans3_Gen_L0Fin3 F a ha0 :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1) := by rw [← hLeftEq]
    _ = 1 := hEntry

theorem leftSimpleRootCoeff_G10TranslatedStageThree_C1
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h01 =
      0 := by
  have hFact := G10Trans3_gen_S1_factorization_aux F a ha0 h01
  have hNeg :
      (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10TranslatedStageThreeGenericMonomial F a ha0 :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10Trans3GenericMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans3_Gen_L1Fin3 F a ha0 :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    simp [G10Trans3_Gen_L1Fin3,
      UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.isValue]
  have hEqC1 :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans3_C1Fin3 F a h01 := by
    unfold G10Trans3_C1Fin3 G10Trans3_C0Fin3 G10Trans3_P3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      Matrix.GeneralLinearGroup.bruhatLeft (G10Trans3_C1Fin3 F a h01) := by
    rw [hEqC1]
  calc leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans3_C1Fin3 F a h01) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by rw [hBL]
    _ = (((G10Trans3_Gen_L1Fin3 F a ha0 :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1) := by rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_G10TranslatedStageThree_C0_not_pos
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageThree_C0 F a ha0 h01
  rw [hMid, fin3G10Trans3GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageThree_C1_not_pos
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageThree_C1 F a ha0 h01
  rw [hMid, fin3G10Trans3GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageThree_zero_C0
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      fin3G10TranslatedStageThreeZeroMonomial F := by
  have hFact := G10Trans3_zero_S0_factorization_aux (F := F) h01
  have hEq :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
      G10Trans3_ZeroC0Fin3 F h01 := by
    unfold G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageThree_zero_C1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      fin3G10TranslatedStageThreeZeroMonomial F := by
  have hFact := G10Trans3_zero_S1_factorization_aux (F := F) h01
  have hEq :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans3_ZeroC1Fin3 F h01 := by
    unfold G10Trans3_ZeroC1Fin3 G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10TranslatedStageThree_zero_C0
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) h01 =
      1 := by
  have hFact := G10Trans3_zero_S0_factorization_aux (F := F) h01
  have hNeg :
      (fin3G10TranslatedStageThreeZeroMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10TranslatedStageThreeZeroMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10Trans3ZeroMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans3_Zero_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 1) := by
    simp [G10Trans3_Zero_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.isValue]
  have hEqC0 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
      G10Trans3_ZeroC0Fin3 F h01 := by
    unfold G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans3_ZeroC0Fin3 F h01) := by
    rw [hEqC0]
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans3_ZeroC0Fin3 F h01) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [hBL]
    _ = (((G10Trans3_Zero_L0Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeftEq]
    _ = 1 := hEntry

theorem leftSimpleRootCoeff_G10TranslatedStageThree_zero_C1
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h01 =
      0 := by
  have hFact := G10Trans3_zero_S1_factorization_aux (F := F) h01
  have hNeg :
      (fin3G10TranslatedStageThreeZeroMonomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (fin3G10TranslatedStageThreeZeroMonomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [fin3G10Trans3ZeroMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans3_Zero_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    simp [G10Trans3_Zero_L1Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply]
  have hEqC1 :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans3_ZeroC1Fin3 F h01 := by
    unfold G10Trans3_ZeroC1Fin3 G10Trans3_ZeroC0Fin3 G10Trans3_ZeroP3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans3_ZeroC1Fin3 F h01) := by
    rw [hEqC1]
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans3_ZeroC1Fin3 F h01) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [hBL]
    _ = (((G10Trans3_Zero_L1Fin3 F : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_G10TranslatedStageThree_zero_C0_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageThree_zero_C0 F h01
  rw [hMid, fin3G10Trans3ZeroMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageThree_zero_C1_not_pos
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) ) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageThree_zero_C1 F h01
  rw [hMid, fin3G10Trans3ZeroMonomial_right_perm]
  decide

end G10TranslatedStageThreeBruhat

section G10TranslatedStageFourBruhat

variable {F : Type*} [Field F]

private theorem G10Trans4_weyl_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (u : Fˣ) :
    Matrix.GeneralLinearGroup.weylSLUnit i j hij1 u =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij2 u := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.weylSLUnit,
    Matrix.SpecialLinearGroup.transvection_coe]

private theorem G10Trans4_transvection_ne_irrel
    {i j : Fin 3} (hij1 hij2 : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.transvection hij1 a =
      Matrix.SpecialLinearGroup.transvection hij2 a := by
  apply Subtype.ext
  rfl

noncomputable def fin3G10TranslatedStageFourGenericMonomial
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    MonomialSL F (Fin 3) :=
  let haInv : a⁻¹ ≠ 0 := inv_ne_zero ha0
  let hNegInv : -a⁻¹ ≠ 0 := neg_ne_zero.mpr haInv
  Matrix.GeneralLinearGroup.torusMonomialSLUnit
      (0 : Fin 3) (2 : Fin 3) (by decide)
      (Units.mk0 (-a⁻¹) hNegInv) *
    fin3TranslatedLowerCycleMonomial F

private theorem fin3G10Trans4GenericMonomial_right_perm
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
      MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  unfold fin3G10TranslatedStageFourGenericMonomial
    fin3TranslatedLowerCycleMonomial
  simp [Matrix.GeneralLinearGroup.torusMonomialSLUnit,
    Matrix.GeneralLinearGroup.weylMonomialSLUnit,
    Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.torusPerm,
    Matrix.GeneralLinearGroup.weylPerm]

private theorem fin3G10Trans4GenericMonomial_inv_perm
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
      MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  have h := fin3G10Trans4GenericMonomial_right_perm
    (F := F) (a := a) (ha0 := ha0)
  have hInv :
      (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ =
        (Equiv.swap (1 : Fin 3) 2 *
          Equiv.swap (0 : Fin 3) 1)⁻¹ := by rw [h]
  rw [hInv, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

private noncomputable def G10Trans4_P4Fin3
    (F : Type*) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
      (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))

private noncomputable def G10Trans4_C0Fin3
    (F : Type*) [Field F] (a : F)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit
      (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
    G10Trans4_P4Fin3 F a

private noncomputable def G10Trans4_C1Fin3
    (F : Type*) [Field F] (a : F)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
    G10Trans4_C0Fin3 F a h12

private noncomputable def G10Trans4_Gen_L0Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
      (by decide) (1 : F) *
    (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
        (by decide) (a⁻¹) *
      UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
        (by decide) (-1 : F))

private noncomputable def G10Trans4_Gen_L1Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (a⁻¹) *
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10Trans4_Gen_R0Fin3
    (F : Type*) [Field F] (a : F) (_ha0 : a ≠ 0) :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      (by decide) (a⁻¹) *
    UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
      (by decide) (-1 : F)

private noncomputable def G10Trans4_Zero_L0Fin3
    (F : Type*) [Field F] :
    upperElementarySubgroup (Fin 3) F :=
  UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
    (by decide) (1 : F)

private noncomputable def G10Trans4_ZeroP3Fin3
    (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
      (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))

private noncomputable def G10Trans4_ZeroC0Fin3
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit
      (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
    G10Trans4_ZeroP3Fin3 F

private noncomputable def G10Trans4_ZeroC1Fin3
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
    G10Trans4_ZeroC0Fin3 F h12

private theorem G10Trans4_elem12_add
    (F : Type*) [Field F] (a b : F) :
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) a *
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) b =
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) (a + b) := by
  apply Subtype.ext
  simp [UpperElementary.coe_elementary,
    Matrix.GeneralLinearGroup.elementary_mul_same]

private theorem G10Trans4_elem12_neg_one_mul_one
    (F : Type*) [Field F] :
    UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) (-1 : F) *
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
        (by decide) (1 : F) =
      (1 : upperElementarySubgroup (Fin 3) F) := by
  have hAdd : (-1 : F) + 1 = 0 := by ring
  calc UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (-1 : F) *
        UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (1 : F)
      = UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) ((-1 : F) + 1) := by
        rw [G10Trans4_elem12_add]
    _ = UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (0 : F) := by rw [hAdd]
    _ = 1 := by
        apply Subtype.ext
        simp [UpperElementary.coe_elementary]

private theorem G10Trans4_P4Fin3_matrix
    (F : Type*) [Field F] (a : F) :
    (G10Trans4_P4Fin3 F a : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; a, 1, -a; -a, -1, 1 + a] := by
  unfold G10Trans4_P4Fin3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]
  ring

private theorem G10Trans4_weyl12_neg_one_matrix
    (F : Type*) [Field F] :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.weylSLUnit,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_weyl12_one_inv_matrix
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ((Matrix.GeneralLinearGroup.weylSLUnit
        (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  have hInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
    calc (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹
        = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
          apply G10Trans4_weyl_ne_irrel
  calc ((Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hInv]
    _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
        rw [G10Trans4_weyl12_neg_one_matrix]

private theorem G10Trans4_C0Fin3_matrix
    (F : Type*) [Field F] (a : F)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (G10Trans4_C0Fin3 F a h12 : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; a, 1, -a - 1; a, 1, -a] := by
  have hW := G10Trans4_weyl12_one_inv_matrix (F := F) h12
  have hP := G10Trans4_P4Fin3_matrix (F := F) (a := a)
  have hC0_def :
      (G10Trans4_C0Fin3 F a h12 : Matrix (Fin 3) (Fin 3) F) =
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_P4Fin3 F a : Matrix (Fin 3) (Fin 3) F) := by
    simp [G10Trans4_C0Fin3, Matrix.SpecialLinearGroup.coe_mul]
  calc (G10Trans4_C0Fin3 F a h12 : Matrix (Fin 3) (Fin 3) F)
      = ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_P4Fin3 F a : Matrix (Fin 3) (Fin 3) F) := hC0_def
    _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] *
        !![1, 0, 0; a, 1, -a; -a, -1, 1 + a] := by rw [hW, hP]
    _ = !![1, 0, 0; a, 1, -a - 1; a, 1, -a] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,
          Fin.sum_univ_three, Fin.isValue]
        ring

private theorem G10Trans4_weyl01_one_matrix
    (F : Type*) [Field F] :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.weylSLUnit,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_lowerCycle_matrix
    (F : Type*) [Field F] :
    (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![0, 1, 0; 0, 0, -1; -1, 0, 0] := by
  have hM :
      monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) =
        Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
    calc monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F)
        = monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ)) *
          monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)) := by
          unfold fin3TranslatedLowerCycleMonomial
          rw [map_mul]
      _ = Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom,
            Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hW12 := G10Trans4_weyl12_neg_one_matrix (F := F)
  have hW01 := G10Trans4_weyl01_one_matrix (F := F)
  have hDef :
      (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
    calc (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hM]
      _ = (Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
        simp [Matrix.SpecialLinearGroup.coe_mul]
  calc (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := hDef
    _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] *
        !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by rw [hW12, hW01]
    _ = !![0, 1, 0; 0, 0, -1; -1, 0, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_torus02_matrix
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    let haInv : a⁻¹ ≠ 0 := inv_ne_zero ha0
    let hNegInv : -a⁻¹ ≠ 0 := neg_ne_zero.mpr haInv
    (Matrix.GeneralLinearGroup.torusSLUnit
        (0 : Fin 3) (2 : Fin 3) (by decide)
        (Units.mk0 (-a⁻¹) hNegInv) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![-a⁻¹, 0, 0; 0, 1, 0; 0, 0, -a] := by
  intro haInv hNegInv
  have hTorus :=
      Matrix.GeneralLinearGroup.torusSLUnit_eq_diag2n
        (F := F) (0 : Fin 3) (2 : Fin 3) (by decide)
        (Units.mk0 (-a⁻¹) hNegInv)
  have hInvNeg : (-a⁻¹ : F)⁻¹ = -a := by
    rw [inv_neg, inv_inv]
  calc (Matrix.GeneralLinearGroup.torusSLUnit
          (0 : Fin 3) (2 : Fin 3) (by decide)
          (Units.mk0 (-a⁻¹) hNegInv) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.SpecialLinearGroup.diag2n
          (by decide : (0 : Fin 3) ≠ 2)
          ((Units.mk0 (-a⁻¹) hNegInv : Fˣ) : F)
          hNegInv :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [hTorus]
    _ = !![-a⁻¹, 0, 0; 0, 1, 0; 0, 0, -a] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.diag2n_coe, hInvNeg,
            Fin.isValue]

private theorem G10Trans4_genericMonomial_matrix
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (monomialSLHom F (Fin 3)
        (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![0, -a⁻¹, 0; 0, 0, -1; a, 0, 0] := by
  have haInv : a⁻¹ ≠ 0 := inv_ne_zero ha0
  have hNegInv : -a⁻¹ ≠ 0 := neg_ne_zero.mpr haInv
  have hM_eq :
      monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) =
        Matrix.GeneralLinearGroup.torusSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide)
            (Units.mk0 (-a⁻¹) hNegInv) *
          monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) := by
    unfold fin3G10TranslatedStageFourGenericMonomial
    rw [map_mul, Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom]
  have hTorus := G10Trans4_torus02_matrix (F := F) (a := a) (ha0 := ha0)
  have hCycle := G10Trans4_lowerCycle_matrix (F := F)
  have hDef :
      (monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        (Matrix.GeneralLinearGroup.torusSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide)
            (Units.mk0 (-a⁻¹) hNegInv) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
    calc (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (Matrix.GeneralLinearGroup.torusSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide)
              (Units.mk0 (-a⁻¹) hNegInv) *
            monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hM_eq]
      _ = (Matrix.GeneralLinearGroup.torusSLUnit
              (0 : Fin 3) (2 : Fin 3) (by decide)
              (Units.mk0 (-a⁻¹) hNegInv) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
        simp [Matrix.SpecialLinearGroup.coe_mul]
  calc (monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.GeneralLinearGroup.torusSLUnit
            (0 : Fin 3) (2 : Fin 3) (by decide)
            (Units.mk0 (-a⁻¹) hNegInv) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3) (fin3TranslatedLowerCycleMonomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := hDef
    _ = !![-a⁻¹, 0, 0; 0, 1, 0; 0, 0, -a] *
        !![0, 1, 0; 0, 0, -1; -1, 0, 0] := by rw [hTorus, hCycle]
    _ = !![0, -a⁻¹, 0; 0, 0, -1; a, 0, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_Gen_L0_matrix
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, -1, a⁻¹; 0, 1, 1; 0, 0, 1] := by
  have hL0 :
      UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (a⁻¹) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 1) (-1 : F)) := by
    unfold G10Trans4_Gen_L0Fin3
    rw [map_mul, map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 3) ≠ 2) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (a⁻¹) *
            Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 1) (-1 : F)) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hL0]
    _ = !![1, -1, a⁻¹; 0, 1, 1; 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_Gen_R0_matrix
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, a⁻¹, -1; 0, 1, 0; 0, 0, 1] := by
  have hR0 :
      UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) =
        Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (a⁻¹) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (-1 : F) := by
    unfold G10Trans4_Gen_R0Fin3
    rw [map_mul,
      toSLHom_elementary_eq_transvection,
      toSLHom_elementary_eq_transvection]
  calc (UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 1) (a⁻¹) *
          Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (-1 : F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hR0]
    _ = !![1, a⁻¹, -1; 0, 1, 0; 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.add_apply, Matrix.single_apply,
            Matrix.one_apply, Matrix.mul_apply,
            Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_L0_M_R_matrix
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0) :
    (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, 0, 0; a, 1, -a - 1; a, 1, -a] := by
  have hL0 := G10Trans4_Gen_L0_matrix (F := F) (a := a) (ha0 := ha0)
  have hM := G10Trans4_genericMonomial_matrix (F := F) (a := a) (ha0 := ha0)
  have hR0 := G10Trans4_Gen_R0_matrix (F := F) (a := a) (ha0 := ha0)
  have haMul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have haInvMul : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have hMR :
      (monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        !![0, -a⁻¹, 0; 0, 0, -1; a, 1, -a] := by
    have hDef :
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val =
          (monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
      simp [Matrix.SpecialLinearGroup.coe_mul]
    calc (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageFourGenericMonomial F a ha0) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := hDef
      _ = !![0, -a⁻¹, 0; 0, 0, -1; a, 0, 0] *
          !![1, a⁻¹, -1; 0, 1, 0; 0, 0, 1] := by rw [hM, hR0]
      _ = !![0, -a⁻¹, 0; 0, 0, -1; a, 1, -a] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue, haMul]
  have hDef2 :
      (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0)) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
    simp [Matrix.SpecialLinearGroup.coe_mul]
  have hAssoc :
      UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) =
      UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0)) := by
    rw [mul_assoc]
  calc (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0)) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hAssoc]
    _ = (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := hDef2
    _ = !![1, -1, a⁻¹; 0, 1, 1; 0, 0, 1] *
        !![0, -a⁻¹, 0; 0, 0, -1; a, 1, -a] := by rw [hL0, hMR]
    _ = !![1, 0, 0; a, 1, -a - 1; a, 1, -a] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
            haInvMul]
        ring

private theorem G10Trans4_gen_S0_factorization_aux
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans4_C0Fin3 F a h12 =
      UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) := by
  have hC0 := G10Trans4_C0Fin3_matrix (F := F) (a := a) (h12 := h12)
  have hLMR := G10Trans4_L0_M_R_matrix (F := F) (a := a) (ha0 := ha0)
  apply Subtype.ext
  calc (G10Trans4_C0Fin3 F a h12 : Matrix (Fin 3) (Fin 3) F)
      = !![1, 0, 0; a, 1, -a - 1; a, 1, -a] := hC0
    _ = (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := hLMR.symm

private theorem G10Trans4_gen_S1_factorization_aux
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans4_C1Fin3 F a h12 =
      UpperElementary.toSLHom (G10Trans4_Gen_L1Fin3 F a ha0) *
        monomialSLHom F (Fin 3)
          (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
        UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) := by
  have hS0 := G10Trans4_gen_S0_factorization_aux
    (F := F) (a := a) (ha0 := ha0) h12
  have hT12 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) =
        UpperElementary.toSLHom
          (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (-1 : F)) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F)
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (1 : Fin 3) < 2)) (-1 : F) := by
          apply G10Trans4_transvection_ne_irrel
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (-1 : F)) := by
          rw [← toSLHom_elementary_eq_transvection]
  have hMul :
      UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
          (by decide) (-1 : F) *
        G10Trans4_Gen_L0Fin3 F a ha0 =
        G10Trans4_Gen_L1Fin3 F a ha0 := by
    calc UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
            (by decide) (-1 : F) *
          G10Trans4_Gen_L0Fin3 F a ha0
        = UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (-1 : F) *
            UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (1 : F) *
            (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
                (by decide) (a⁻¹) *
              UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) := by
          unfold G10Trans4_Gen_L0Fin3
          simp only [mul_assoc]
      _ = (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (-1 : F) *
            UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
              (by decide) (1 : F)) *
            (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
                (by decide) (a⁻¹) *
              UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) := by simp only [mul_assoc]
      _ = (1 : upperElementarySubgroup (Fin 3) F) *
            (UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
                (by decide) (a⁻¹) *
              UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
                (by decide) (-1 : F)) := by
          rw [G10Trans4_elem12_neg_one_mul_one]
      _ = UpperElementary.elementary (0 : Fin 3) (2 : Fin 3)
              (by decide) (a⁻¹) *
            UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
              (by decide) (-1 : F) := by simp
      _ = G10Trans4_Gen_L1Fin3 F a ha0 := rfl
  have hMulSL :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) =
        UpperElementary.toSLHom (G10Trans4_Gen_L1Fin3 F a ha0) := by
    calc Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0)
        = UpperElementary.toSLHom
              (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F)) *
            UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) := by
          rw [hT12]
      _ = UpperElementary.toSLHom
            (UpperElementary.elementary (1 : Fin 3) (2 : Fin 3)
                (by decide) (-1 : F) *
              G10Trans4_Gen_L0Fin3 F a ha0) := by rw [← map_mul]
      _ = UpperElementary.toSLHom (G10Trans4_Gen_L1Fin3 F a ha0) := by
          rw [hMul]
  calc G10Trans4_C1Fin3 F a h12
      = Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          G10Trans4_C0Fin3 F a h12 := rfl
    _ = Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          (UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0) *
            monomialSLHom F (Fin 3)
              (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
            UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0)) := by
        rw [hS0]
    _ = (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          UpperElementary.toSLHom (G10Trans4_Gen_L0Fin3 F a ha0)) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) := by
        simp only [mul_assoc]
    _ = UpperElementary.toSLHom (G10Trans4_Gen_L1Fin3 F a ha0) *
          monomialSLHom F (Fin 3)
            (fin3G10TranslatedStageFourGenericMonomial F a ha0) *
          UpperElementary.toSLHom (G10Trans4_Gen_R0Fin3 F a ha0) := by
        rw [hMulSL]

private theorem G10Trans4_ZeroP3_matrix
    (F : Type*) [Field F] :
    (G10Trans4_ZeroP3Fin3 F : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; 0, -1, 1] := by
  unfold G10Trans4_ZeroP3Fin3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_ZeroC0_matrix
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, -1; 0, 1, 0] := by
  have hW := G10Trans4_weyl12_one_inv_matrix (F := F) h12
  have hP := G10Trans4_ZeroP3_matrix (F := F)
  have hC0 :
      (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) =
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_ZeroP3Fin3 F : Matrix (Fin 3) (Fin 3) F) := by
    simp [G10Trans4_ZeroC0Fin3, G10Trans4_ZeroP3Fin3,
      Matrix.SpecialLinearGroup.coe_mul]
  calc (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F)
      = ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_ZeroP3Fin3 F : Matrix (Fin 3) (Fin 3) F) := hC0
    _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] *
        !![1, 0, 0; 0, 1, 0; 0, -1, 1] := by rw [hW, hP]
    _ = !![1, 0, 0; 0, 1, -1; 0, 1, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_ZeroC1_matrix
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    (G10Trans4_ZeroC1Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  have hC0 := G10Trans4_ZeroC0_matrix (F := F) (h12 := h12)
  have hC1 :
      (G10Trans4_ZeroC1Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) =
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) := by
    simp [G10Trans4_ZeroC1Fin3, Matrix.SpecialLinearGroup.coe_mul]
  have hT12 :
      (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        !![1, 0, 0; 0, 1, -1; 0, 0, 1] := by
    have hNe : h12.ne =
        ne_of_lt (show (1 : Fin 3) < 2 by decide) := by
      apply Decidable.by_contra
      intro h
      simp_all
    calc (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (show (1 : Fin 3) < 2 by decide)) (-1 : F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [hNe]
      _ = !![1, 0, 0; 0, 1, -1; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.SpecialLinearGroup.transvection_coe, Fin.isValue]
  calc (G10Trans4_ZeroC1Fin3 F h12 : Matrix (Fin 3) (Fin 3) F)
      = (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F) := hC1
    _ = !![1, 0, 0; 0, 1, -1; 0, 0, 1] *
        !![1, 0, 0; 0, 1, -1; 0, 1, 0] := by rw [hT12, hC0]
    _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue]

private theorem G10Trans4_Zero_L0_matrix
    (F : Type*) [Field F] :
    (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
      Matrix.SpecialLinearGroup (Fin 3) F).val =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := by
  have h :
      UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 (F := F)) =
        Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (1 : F) := by
    unfold G10Trans4_Zero_L0Fin3
    rw [toSLHom_elementary_eq_transvection]
  calc (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val
      = (Matrix.SpecialLinearGroup.transvection
          (by decide : (1 : Fin 3) ≠ 2) (1 : F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [h]
    _ = !![1, 0, 0; 0, 1, 1; 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, Fin.isValue]

private theorem G10Trans4_zero_S0_factorization_aux
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans4_ZeroC0Fin3 F h12 =
      UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) := by
  have hC0 := G10Trans4_ZeroC0_matrix (F := F) (h12 := h12)
  have hL0 := G10Trans4_Zero_L0_matrix (F := F)
  have hM :
      (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
    have hMono :
        monomialSLHom F (Fin 3) (fin3G01Monomial F) =
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
      unfold fin3G01Monomial
      rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
    calc (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hMono]
      _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
          rw [G10Trans4_weyl12_neg_one_matrix]
  have hOne : (UpperElementary.toSLHom
      (1 : upperElementarySubgroup (Fin 3) F) :
      Matrix.SpecialLinearGroup (Fin 3) F).val = 1 := by
    simp [Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  have hDef :
      (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
    calc (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G01Monomial F) *
          UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) *
            monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [hOne, Matrix.mul_one]
  calc (G10Trans4_ZeroC0Fin3 F h12 : Matrix (Fin 3) (Fin 3) F)
      = !![1, 0, 0; 0, 1, -1; 0, 1, 0] := hC0
    _ = !![1, 0, 0; 0, 1, 1; 0, 0, 1] *
        !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,
          Fin.sum_univ_three, Fin.isValue]
    _ = (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val *
        (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hL0, hM]
    _ = (UpperElementary.toSLHom (G10Trans4_Zero_L0Fin3 F) *
          monomialSLHom F (Fin 3) (fin3G01Monomial F) *
          UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := hDef.symm

private theorem G10Trans4_zero_S1_factorization_aux
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    G10Trans4_ZeroC1Fin3 F h12 =
      UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) := by
  have hC1 := G10Trans4_ZeroC1_matrix (F := F) (h12 := h12)
  have hM :
      (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
    have hMono :
        monomialSLHom F (Fin 3) (fin3G01Monomial F) =
          Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) := by
      unfold fin3G01Monomial
      rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
    calc (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by rw [hMono]
      _ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
          rw [G10Trans4_weyl12_neg_one_matrix]
  have hOne : (UpperElementary.toSLHom
      (1 : upperElementarySubgroup (Fin 3) F) :
      Matrix.SpecialLinearGroup (Fin 3) F).val = 1 := by
    simp [Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  have hDef :
      (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val =
        (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
    calc (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
          monomialSLHom F (Fin 3) (fin3G01Monomial F) *
          UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val
        = (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
            monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val *
          (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = 1 * (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
            Matrix.SpecialLinearGroup (Fin 3) F).val * 1 := by
          rw [hOne]
      _ = (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
          Matrix.SpecialLinearGroup (Fin 3) F).val := by
          rw [Matrix.one_mul, Matrix.mul_one]
  calc (G10Trans4_ZeroC1Fin3 F h12 : Matrix (Fin 3) (Fin 3) F)
      = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := hC1
    _ = (monomialSLHom F (Fin 3) (fin3G01Monomial F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := hM.symm
    _ = (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) (fin3G01Monomial F) *
        UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) :
        Matrix.SpecialLinearGroup (Fin 3) F).val := hDef.symm

theorem bruhatMiddle_G10TranslatedStageFour_D0
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      fin3G10TranslatedStageFourGenericMonomial F a ha0 := by
  have hFact := G10Trans4_gen_S0_factorization_aux F a ha0 h12
  have hEq :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans4_C0Fin3 F a h12 := by
    unfold G10Trans4_C0Fin3 G10Trans4_P4Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageFour_D1
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) =
      fin3G10TranslatedStageFourGenericMonomial F a ha0 := by
  have hFact := G10Trans4_gen_S1_factorization_aux F a ha0 h12
  have hEq :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      G10Trans4_C1Fin3 F a h12 := by
    unfold G10Trans4_C1Fin3 G10Trans4_C0Fin3 G10Trans4_P4Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10TranslatedStageFour_D0
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h12 =
      1 := by
  have hFact := G10Trans4_gen_S0_factorization_aux F a ha0 h12
  have hNeg :
      (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10Trans4GenericMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans4_Gen_L0Fin3 F a ha0 :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 1) := by
    simp [G10Trans4_Gen_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
      Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  have hEqC0 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans4_C0Fin3 F a h12 := by
    unfold G10Trans4_C0Fin3 G10Trans4_P4Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans4_C0Fin3 F a h12) := by rw [hEqC0]
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans4_C0Fin3 F a h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [hBL]
    _ = (((G10Trans4_Gen_L0Fin3 F a ha0 :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [← hLeftEq]
    _ = 1 := hEntry

theorem leftSimpleRootCoeff_G10TranslatedStageFour_D1
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) h12 =
      0 := by
  have hFact := G10Trans4_gen_S1_factorization_aux F a ha0 h12
  have hNeg :
      (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G10TranslatedStageFourGenericMonomial F a ha0 :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G10Trans4GenericMonomial_inv_perm]
    decide
  have hEntry :
      (((G10Trans4_Gen_L1Fin3 F a ha0 :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
    simp [G10Trans4_Gen_L1Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.mul_apply,
      Fin.isValue, Matrix.add_apply, Matrix.one_apply]
  have hEqC1 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      G10Trans4_C1Fin3 F a h12 := by
    unfold G10Trans4_C1Fin3 G10Trans4_C0Fin3 G10Trans4_P4Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hBL :
      Matrix.GeneralLinearGroup.bruhatLeft
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) =
      Matrix.GeneralLinearGroup.bruhatLeft
        (G10Trans4_C1Fin3 F a h12) := by rw [hEqC1]
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) h12
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans4_C1Fin3 F a h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [hBL]
    _ = (((G10Trans4_Gen_L1Fin3 F a ha0 :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_G10TranslatedStageFour_D0_not_pos
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageFour_D0 F a ha0 h12
  rw [hMid, fin3G10Trans4GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageFour_D1_not_pos
    (F : Type*) [Field F] (a : F) (ha0 : a ≠ 0)
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageFour_D1 F a ha0 h12
  rw [hMid, fin3G10Trans4GenericMonomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageFour_zero_D0
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      fin3G01Monomial F := by
  have hFact := G10Trans4_zero_S0_factorization_aux (F := F) h12
  have hEq :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans4_ZeroC0Fin3 F h12 := by
    unfold G10Trans4_ZeroC0Fin3 G10Trans4_ZeroP3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem bruhatMiddle_G10TranslatedStageFour_zero_D1
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      fin3G01Monomial F := by
  have hFact := G10Trans4_zero_S1_factorization_aux (F := F) h12
  have hEq :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans4_ZeroC1Fin3 F h12 := by
    unfold G10Trans4_ZeroC1Fin3 G10Trans4_ZeroC0Fin3
      G10Trans4_ZeroP3Fin3
    rfl
  rw [hEq]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim
    _ _ _ _ hFact

theorem leftSimpleRootCoeff_G10TranslatedStageFour_zero_D0
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h12 =
      1 := by
  have hFact := G10Trans4_zero_S0_factorization_aux (F := F) h12
  have hNeg :
      (fin3G01Monomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G01Monomial_inv_perm]
    decide
  have hEntry :
      ((G10Trans4_Zero_L0Fin3 F :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 1 := by
    simp [G10Trans4_Zero_L0Fin3, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hEqC0 :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      G10Trans4_ZeroC0Fin3 F h12 := by
    unfold G10Trans4_ZeroC0Fin3 G10Trans4_ZeroP3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hCoeffEq :
      leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h12 =
      leftSimpleRootCoeff F 3 (G10Trans4_ZeroC0Fin3 F h12) h12 := by
    rw [hEqC0]
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) h12
      = leftSimpleRootCoeff F 3 (G10Trans4_ZeroC0Fin3 F h12) h12 :=
        hCoeffEq
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans4_ZeroC0Fin3 F h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = (((G10Trans4_Zero_L0Fin3 F :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [← hLeftEq]
    _ = 1 := hEntry

theorem leftSimpleRootCoeff_G10TranslatedStageFour_zero_D1
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h12 =
      0 := by
  have hFact := G10Trans4_zero_S1_factorization_aux (F := F) h12
  have hNeg :
      (fin3G01Monomial F :
        MonomialBase Fˣ (Fin 3)).right⁻¹ (2 : Fin 3) <
        (fin3G01Monomial F :
          MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) := by
    rw [fin3G01Monomial_inv_perm]
    decide
  have hEntry :
      (((1 : upperElementarySubgroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    simp
  have hEqC1 :
      Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      G10Trans4_ZeroC1Fin3 F h12 := by
    unfold G10Trans4_ZeroC1Fin3 G10Trans4_ZeroC0Fin3
      G10Trans4_ZeroP3Fin3
    rfl
  have hLeftEq :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h12 hNeg
  have hCoeffEq :
      leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h12 =
      leftSimpleRootCoeff F 3 (G10Trans4_ZeroC1Fin3 F h12) h12 := by
    rw [hEqC1]
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) h12
      = leftSimpleRootCoeff F 3 (G10Trans4_ZeroC1Fin3 F h12) h12 :=
        hCoeffEq
    _ = (((Matrix.GeneralLinearGroup.bruhatLeft
          (G10Trans4_ZeroC1Fin3 F h12) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := rfl
    _ = ((((1 : upperElementarySubgroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 2) := by rw [← hLeftEq]
    _ = 0 := hEntry

theorem bruhatMiddle_G10TranslatedStageFour_zero_D0_not_pos
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageFour_zero_D0 F h12
  rw [hMid, fin3G01Monomial_right_perm]
  decide

theorem bruhatMiddle_G10TranslatedStageFour_zero_D1_not_pos
    (F : Type*) [Field F]
    (h12 : (1 : Fin 3) ⋖ (2 : Fin 3)) :
    ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h12.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) h12.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
  have hMid := bruhatMiddle_G10TranslatedStageFour_zero_D1 F h12
  rw [hMid, fin3G01Monomial_right_perm]
  decide

end G10TranslatedStageFourBruhat

theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) h01 = 0 := by
  let L : upperElementarySubgroup (Fin 3) F := 1
  let M : MonomialSL F (Fin 3) :=
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-1 : F)
  have hWeylInv :
    (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      monomialSLHom F (Fin 3) M := by
    calc _ = (monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)))⁻¹ := by
          rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
      _ = _ := by rw [← map_inv]
  have hTrans :
    Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
        UpperElementary.toSLHom R := by
    calc _ = Matrix.SpecialLinearGroup.transvection (ne_of_lt h01.lt) (-1 : F) := by
          apply Subtype.ext; rfl
      _ = _ := (toSLHom_elementary_eq_transvection h01.lt (-1 : F)).symm
  have hFact :
    (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
      UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    calc _ = monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by rw [hWeylInv, hTrans]
      _ = _ := by simp [L]
  have hMRight :
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ) :
        MonomialBase Fˣ (Fin 3)).right = Equiv.swap (0 : Fin 3) (1 : Fin 3) := by
    simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit, Matrix.GeneralLinearGroup.weylPerm]
  have hMBaseRight :
    (M : MonomialBase Fˣ (Fin 3)).right = Equiv.swap (0 : Fin 3) (1 : Fin 3) := by
    calc _ = ((Matrix.GeneralLinearGroup.weylMonomialSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ :
          MonomialBase Fˣ (Fin 3)).right := rfl
      _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ := by
          rw [Matrix.GeneralLinearGroup.monomialBase_inv_right]
      _ = _ := by rw [hMRight, Equiv.swap_inv]
  have hNeg :
    (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMBaseRight, Equiv.swap_inv]; decide
  have hEntry :
    (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    simp [L]
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) :
            Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg]
    _ = 0 := hEntry

theorem bruhatMiddle_weyl01_inv_mul_transvection01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
  let L : upperElementarySubgroup (Fin 3) F := 1
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-1 : F)
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        monomialSLHom F (Fin 3) M := by
    calc _ = Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = _ := by rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hTrans :
    Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
        UpperElementary.toSLHom R := by
    calc _ = Matrix.SpecialLinearGroup.transvection (ne_of_lt h01.lt) (-1 : F) := by
          apply Subtype.ext; rfl
      _ = _ := (toSLHom_elementary_eq_transvection h01.lt (-1 : F)).symm
  have hFact :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
      UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    calc _ = monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by rw [hWeylInv, hTrans]
      _ = _ := by simp [L]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

theorem leftSimpleRootCoeff_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftSimpleRootCoeff F 3
      (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) h01 = -1 := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : F)
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ)
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : F)
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hM_eq :
      monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
      UpperElementary.toSLHom L *
        monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [hWeylInv, hM_eq]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  have hMRight :
      (M : MonomialBase Fˣ (Fin 3)).right = Equiv.swap (0 : Fin 3) 1 := by
    simp [M, Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit, Matrix.GeneralLinearGroup.weylPerm]
  have hMInv :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ = Equiv.swap (0 : Fin 3) 1 := by
    rw [hMRight, Equiv.swap_inv]
  have hNeg :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMInv]; decide
  have hEntry :
      (((L : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = -1) := by
    simp [L, UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply]
  have hLeft :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
            (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) :
          Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeft]
    _ = -1 := hEntry

theorem bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-1 : F)
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-1 : F)
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hM_eq :
      monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact :
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) =
      UpperElementary.toSLHom L *
        monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [hWeylInv, hM_eq]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection01_neg
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (a : F) :
    leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-a)) h01 = 0 := by
  let L : upperElementarySubgroup (Fin 3) F := 1
  let M : MonomialSL F (Fin 3) :=
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-a)
  have hWeylInv :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      monomialSLHom F (Fin 3) M := by
    calc _ = (monomialSLHom F (Fin 3)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)))⁻¹ := by
          rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
      _ = _ := by rw [← map_inv]
  have hTrans :
    Matrix.SpecialLinearGroup.transvection h01.ne (-a) =
        UpperElementary.toSLHom R := by
    calc _ = Matrix.SpecialLinearGroup.transvection
          (ne_of_lt h01.lt) (-a) := by
          apply Subtype.ext; rfl
      _ = _ := (toSLHom_elementary_eq_transvection h01.lt (-a)).symm
  have hFact :
    (Matrix.GeneralLinearGroup.weylSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-a) =
      UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    calc _ = monomialSLHom F (Fin 3) M *
          UpperElementary.toSLHom R := by
          rw [hWeylInv, hTrans]
      _ = _ := by simp [L]
  have hMRight :
    (Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ) :
        MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) (1 : Fin 3) := by
    simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hMBaseRight :
    (M : MonomialBase Fˣ (Fin 3)).right =
        Equiv.swap (0 : Fin 3) (1 : Fin 3) := by
    calc _ = ((Matrix.GeneralLinearGroup.weylMonomialSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ :
          MonomialBase Fˣ (Fin 3)).right := rfl
      _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ) :
          MonomialBase Fˣ (Fin 3)).right⁻¹ := by
          rw [Matrix.GeneralLinearGroup.monomialBase_inv_right]
      _ = _ := by rw [hMRight, Equiv.swap_inv]
  have hNeg :
    (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMBaseRight, Equiv.swap_inv]; decide
  have hEntry :
    (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    simp [L]
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-a)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection h01.ne (-a)) :
            Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
          hFact h01 hNeg]
    _ = 0 := hEntry

/-- For `h01 : (0 : Fin 3) ⋖ (1 : Fin 3)` and arbitrary `a : F`,
`bruhatMiddle` of `(weylSLUnit 0 1 (1:Fˣ))⁻¹ * transvection (-a)` is
`weylMonomialSLUnit 0 1 (-1:Fˣ)`, independent of `a` (incl. `a = 0`,
char 2). -/
theorem bruhatMiddle_weyl01_inv_mul_transvection01_neg
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (a : F) :
    Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-a)) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
  let L : upperElementarySubgroup (Fin 3) F := 1
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-a)
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        monomialSLHom F (Fin 3) M := by
    calc _ = Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
      _ = _ := by
          rw [Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hTrans :
      Matrix.SpecialLinearGroup.transvection h01.ne (-a) =
        UpperElementary.toSLHom R := by
    calc _ = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt h01.lt) (-a) := by
          apply Subtype.ext; rfl
      _ = _ := (toSLHom_elementary_eq_transvection h01.lt (-a)).symm
  have hFact :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-a) =
      UpperElementary.toSLHom L *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    calc _ = monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
          rw [hWeylInv, hTrans]
      _ = _ := by simp [L]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

/-- Denominator coefficient in the negative Bruhat branch
for `Fin 3`: left root `0 ⋖ 1`. For `u : Fˣ`,
`(w₀₁ 1)⁻¹ * T₀₁(u) * w₀₁(-1)` has left coefficient
`-(u⁻¹)` and lies in the negative branch; proof is
characteristic-two valid, using only `w(1)⁻¹ = w(-1)`. -/
theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u : Fˣ) :
    leftSimpleRootCoeff F 3
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) h01 =
      -(↑u⁻¹ : F) := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹))
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hMEq :
      monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
      UpperElementary.toSLHom L *
        monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [hWeylInv, hMEq]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  have hMRight :
      (M : MonomialBase Fˣ (Fin 3)).right =
        Equiv.swap (0 : Fin 3) 1 := by
    simp [M, Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hMInv :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ =
        Equiv.swap (0 : Fin 3) 1 := by
    rw [hMRight, Equiv.swap_inv]
  have hNeg :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMInv]; decide
  have hEntry :
      (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = -(↑u⁻¹ : F)) := by
    simp [L, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary,
      Matrix.add_apply]
  have hLeft :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
      hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← hLeft]
    _ = -(↑u⁻¹ : F) := hEntry

/-- Denominator middle in the negative Bruhat branch
for `Fin 3`: left root `0 ⋖ 1`. For `u : Fˣ`,
`(w₀₁ 1)⁻¹ * T₀₁(u) * w₀₁(-1)` has middle
`weylMonomialSLUnit 0 1 (-(u⁻¹ : Fˣ))`; proof is
characteristic-two valid, using only `w(1)⁻¹ = w(-1)`. -/
theorem bruhatMiddle_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u : Fˣ) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹))
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  have hWeylInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hMEq :
      monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
      UpperElementary.toSLHom L *
        monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [hWeylInv, hMEq]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

/-- Four-factor numerator `0 ⋖ 1` left coefficient zero for `Fin 3`.
For `h01 : (0 : Fin 3) ⋖ (1 : Fin 3)` and `u : Fˣ`, the product
`T₀₁(↑u⁻¹) * (w₀₁ 1)⁻¹ * T₀₁(↑u) * w₀₁(-1)` has `leftSimpleRootCoeff = 0`;
exact product order and `⁻¹` orientation preserved, char 2 valid,
`u = 1, -1` safe; middle established separately. -/
theorem leftSimpleRootCoeff_transvection01_inv_mul_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u : Fˣ) :
    leftSimpleRootCoeff F 3
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) h01 = 0 := by
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹))
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  have hWInv :
      (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hMEq :
      monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact :
      Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
      UpperElementary.toSLHom
          (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [hWInv, hMEq]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.isValue,
        R, UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  have hMRight :
      (M : MonomialBase Fˣ (Fin 3)).right =
        Equiv.swap (0 : Fin 3) 1 := by
    simp [M, Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hMInv :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ =
        Equiv.swap (0 : Fin 3) 1 := by
    rw [hMRight, Equiv.swap_inv]
  have hNeg :
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
        (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMInv]; decide
  have hEntry :
      (((1 : upperElementarySubgroup (Fin 3) F) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
    simp
  have hLeft :=
      Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg
        hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
          Matrix.GeneralLinearGroup.weylSLUnit
            (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            (Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
            Matrix.GeneralLinearGroup.weylSLUnit
              (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) :
          Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((1 : upperElementarySubgroup (Fin 3) F) :
        Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1 := by
      rw [← hLeft]
    _ = 0 := hEntry

/-- Four-factor numerator middle: `T(u⁻¹)*(w 1)⁻¹*T(u)*w(-1)` has middle
`weylMonomial 0 1 (-(u⁻¹))`; order/`⁻¹`/unit preserved, char2 and `±1` safe. -/
theorem bruhatMiddle_transvection01_inv_mul_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u : Fˣ) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
  let M : MonomialSL F (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialSLUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹))
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3)
      h01.lt (-(↑u⁻¹ : F))
  have hWInv : (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [Matrix.GeneralLinearGroup.weylSLUnit_inv]
  have hMEq : monomialSLHom F (Fin 3) M =
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹)) := by
    rw [← Matrix.GeneralLinearGroup.weylSLUnit_eq_monomialSLHom]
  have hFact : Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (↑u : F) *
        Matrix.GeneralLinearGroup.weylSLUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) =
      UpperElementary.toSLHom
          (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [hWInv, hMEq]
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.weylSLUnit,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.add_apply,
        Matrix.single_apply, Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.isValue, R,
        UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ _ _ _ hFact

theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection01_neg_one_mul_torus01
    (F : Type*) [Field F] (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u : Fˣ) :
    leftSimpleRootCoeff F 3 ((weylSLUnit (0 : Fin 3) (1 : Fin 3)
      h01.ne (1 : Fˣ))⁻¹ * SpecialLinearGroup.transvection h01.ne (-1 : F) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne u) h01 = 0 := by
  let M := weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹))
  let R := UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt
    (-(↑u⁻¹ : F) * ↑u⁻¹)
  have hFact : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      SpecialLinearGroup.transvection h01.ne (-1 : F) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne u =
      UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
      monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [weylSLUnit_inv, ← weylSLUnit_eq_monomialSLHom]
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [weylSLUnit, torusSLUnit, SpecialLinearGroup.transvection_coe,
        SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.isValue, R, UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.coe_elementary,
        UpperElementary.coe_toSLHom]
  have hNeg : (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    have hR : (M : MonomialBase Fˣ (Fin 3)).right =
        Equiv.swap (0 : Fin 3) 1 := by
      simp [M, weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]
    rw [hR, Equiv.swap_inv]; decide
  calc leftSimpleRootCoeff F 3 ((weylSLUnit (0 : Fin 3) (1 : Fin 3)
        h01.ne (1 : Fˣ))⁻¹ * SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne u) h01
      = (((bruhatLeft ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne
        (1 : Fˣ))⁻¹ * SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne u) :
        Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        0 1) := rfl
    _ = 0 := by
        rw [← SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg]; simp

theorem
  leftSimpleRootCoeff_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one_mul_torus01
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (v : Fˣ) :
    leftSimpleRootCoeff F 3
      (SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01 = -1 := by
  let L := UpperElementary.elementary 0 1 h01.lt (-1 : F)
  let M := weylMonomialSLUnit 0 1 h01.ne (-(v⁻¹))
  let R := UpperElementary.elementary 0 1 h01.lt (-(↑v⁻¹ : F) * ↑v⁻¹)
  have hFact : SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit 0 1 h01.ne v =
      UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [weylSLUnit_inv, ← weylSLUnit_eq_monomialSLHom]
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [weylSLUnit, torusSLUnit, SpecialLinearGroup.transvection_coe,
        SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary, coe_elementary,
        UpperElementary.coe_toSLHom]
  have hNeg : (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    have : (M : MonomialBase Fˣ (Fin 3)).right = Equiv.swap (0 : Fin 3) 1 := by
      simp [M, weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]
    rw [show (M : MonomialBase Fˣ (Fin 3)).right⁻¹ = Equiv.swap (0 : Fin 3) 1
      from by rw [this, Equiv.swap_inv]]
    decide
  calc leftSimpleRootCoeff F 3
        (SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          SpecialLinearGroup.transvection h01.ne (-1 : F) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01
      = (((bruhatLeft (SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          SpecialLinearGroup.transvection h01.ne (-1 : F) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) :
          GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := by
        rw [← SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg]
    _ = -1 := by simp [L, UpperElementary.coe_elementary, coe_elementary, Matrix.add_apply]

theorem
  bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one_mul_torus01
    (F : Type*) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (v : Fˣ) :
    bruhatMiddle
      (SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) =
      weylMonomialSLUnit 0 1 h01.ne (-(v⁻¹)) := by
  let L := UpperElementary.elementary 0 1 h01.lt (-1 : F)
  let M := weylMonomialSLUnit 0 1 h01.ne (-(v⁻¹))
  let R := UpperElementary.elementary 0 1 h01.lt (-(↑v⁻¹ : F) * ↑v⁻¹)
  have hFact : SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit 0 1 h01.ne v =
      UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
        UpperElementary.toSLHom R := by
    rw [weylSLUnit_inv, ← weylSLUnit_eq_monomialSLHom]
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [weylSLUnit, torusSLUnit, SpecialLinearGroup.transvection_coe,
        SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.single_apply,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.isValue,
        L, R, UpperElementary.coe_elementary, coe_elementary,
        UpperElementary.coe_toSLHom]
  exact bruhatMiddle_factorization_elim _ L M R hFact

end MatsumotoBruhatLeftTransition
