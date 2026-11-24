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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRoot

@[expose] public section

open Matrix
open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

section WeylRealization

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

private lemma weylGLUnit_val_eq_sum (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (weylGLUnit (R := R) i j hij u : Matrix ι ι R) =
      1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
  have hA : (elementary i j hij (u : R) : Matrix ι ι R) =
      1 + Matrix.single i j (u : R) := rfl
  have hB : (elementary j i hij.symm (-(↑u⁻¹ : R)) : Matrix ι ι R) =
      1 + Matrix.single j i (-(↑u⁻¹ : R)) := rfl
  have hC : (elementary i j hij (u : R) : Matrix ι ι R) =
      1 + Matrix.single i j (u : R) := rfl
  have hAB : Matrix.single i j (u : R) * Matrix.single j i (-(↑u⁻¹ : R)) =
      Matrix.single i i (-1 : R) := by
    calc Matrix.single i j (u : R) * Matrix.single j i (-(↑u⁻¹ : R))
        = Matrix.single i i ((u : R) * (-(↑u⁻¹ : R))) := by
          simp [Matrix.single_mul_single_same]
      _ = Matrix.single i i (-1 : R) := by
          have : (u : R) * (-(↑u⁻¹ : R)) = -1 := by
            have h1 : (u : R) * (↑u⁻¹ : R) = 1 := by
              calc (u : R) * (↑u⁻¹ : R) = ((u * u⁻¹ : Rˣ) : R) := by rw [Units.val_mul]
                _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
                _ = 1 := rfl
            calc (u : R) * (-(↑u⁻¹ : R)) = -((u : R) * (↑u⁻¹ : R)) := by rw [mul_neg]
              _ = -1 := by rw [h1]
          rw [this]
  have hBC : Matrix.single j i (-(↑u⁻¹ : R)) * Matrix.single i j (u : R) =
      Matrix.single j j (-1 : R) := by
    calc Matrix.single j i (-(↑u⁻¹ : R)) * Matrix.single i j (u : R)
        = Matrix.single j j ((-(↑u⁻¹ : R)) * (u : R)) := by
          simp [Matrix.single_mul_single_same]
      _ = Matrix.single j j (-1 : R) := by
          have : (-(↑u⁻¹ : R)) * (u : R) = -1 := by
            have h1 : (↑u⁻¹ : R) * (u : R) = 1 := by
              calc (↑u⁻¹ : R) * (u : R) = ((u⁻¹ * u : Rˣ) : R) := by rw [Units.val_mul]
                _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
                _ = 1 := rfl
            calc (-(↑u⁻¹ : R)) * (u : R) = -((↑u⁻¹ : R) * (u : R)) := by rw [neg_mul]
              _ = -1 := by rw [h1]
          rw [this]
  have hAC : Matrix.single i j (u : R) * Matrix.single i j (u : R) =
      (0 : Matrix ι ι R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have hAB_C : Matrix.single i i (-1 : R) * Matrix.single i j (u : R) =
      Matrix.single i j (-(u : R)) := by
    calc Matrix.single i i (-1 : R) * Matrix.single i j (u : R)
        = Matrix.single i j ((-1 : R) * (u : R)) := by
          simp [Matrix.single_mul_single_same]
      _ = Matrix.single i j (-(u : R)) := by rw [neg_one_mul]
  -- Expand product (1+A)(1+B)(1+C)
  have h12 : (1 + Matrix.single i j (u : R)) *
      (1 + Matrix.single j i (-(↑u⁻¹ : R))) =
      1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R) := by
    calc (1 + Matrix.single i j (u : R)) * (1 + Matrix.single j i (-(↑u⁻¹ : R)))
        = 1 * (1 + Matrix.single j i (-(↑u⁻¹ : R))) +
          Matrix.single i j (u : R) * (1 + Matrix.single j i (-(↑u⁻¹ : R))) := by
          rw [add_mul]
      _ = 1 + Matrix.single j i (-(↑u⁻¹ : R)) +
          Matrix.single i j (u : R) + Matrix.single i i (-1 : R) := by
          simp only [mul_add, one_mul, mul_one, hAB]
          abel
      _ = 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
          Matrix.single i i (-1 : R) := by abel
  have hAC_zero : Matrix.single i j (u : R) * Matrix.single i j (u : R) =
      (0 : Matrix ι ι R) := hAC
  -- Multiply by third factor
  calc (weylGLUnit (R := R) i j hij u : Matrix ι ι R)
      = (1 + Matrix.single i j (u : R)) *
        (1 + Matrix.single j i (-(↑u⁻¹ : R))) *
        (1 + Matrix.single i j (u : R)) := by simp [weylGLUnit, coe_elementary]
    _ = (1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R)) * (1 + Matrix.single i j (u : R)) := by rw [h12]
    _ = (1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R)) * 1 +
        (1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
          Matrix.single i i (-1 : R)) * Matrix.single i j (u : R) := by rw [mul_add]
    _ = _ := by
        have h1 : (1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
            Matrix.single i i (-1 : R)) * Matrix.single i j (u : R) =
            Matrix.single i j (u : R) + Matrix.single j j (-1 : R) +
              Matrix.single i j (-(u : R)) := by
          calc (1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
              Matrix.single i i (-1 : R)) * Matrix.single i j (u : R)
              = 1 * Matrix.single i j (u : R) +
                Matrix.single i j (u : R) * Matrix.single i j (u : R) +
                Matrix.single j i (-(↑u⁻¹ : R)) * Matrix.single i j (u : R) +
                Matrix.single i i (-1 : R) * Matrix.single i j (u : R) := by
                simp only [add_mul]
            _ = Matrix.single i j (u : R) + 0 + Matrix.single j j (-1 : R) +
                Matrix.single i j (-(u : R)) := by
                simp [one_mul, hAC, hBC, hAB_C]
            _ = Matrix.single i j (u : R) + Matrix.single j j (-1 : R) +
                Matrix.single i j (-(u : R)) := by abel
        simp only [mul_one, h1]
        have hAdd : Matrix.single i j (u : R) + Matrix.single i j (-(u : R)) = 0 := by
          rw [← single_add, add_neg_cancel, single_zero]
        calc 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
            Matrix.single i i (-1 : R) +
            (Matrix.single i j (u : R) + Matrix.single j j (-1 : R) +
              Matrix.single i j (-(u : R)))
            = 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
              Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) +
              (Matrix.single i j (u : R) + Matrix.single i j (-(u : R))) := by abel
          _ = 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
              Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by rw [hAdd, add_zero]
          _ = 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
              Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by rfl

private lemma monomialWeyl_val_eq_sum (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) : Matrix ι ι R) =
      1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
  have hCoe : (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) : Matrix ι ι R) =
      Matrix.diagonal (fun k => (weylWeightUnit i j hij u k : R)) *
        ((Equiv.swap i j)⁻¹).permMatrix R := by
    simp [weylMonomialBaseUnit, weylPerm]
  have hSwapInv : ((Equiv.swap i j)⁻¹) = Equiv.swap i j := by simp
  rw [hCoe, hSwapInv]
  ext r c
  have hWeylWeight : (weylWeightUnit i j hij u r : R) =
      if r = i then (u : R) else if r = j then (-(↑u⁻¹ : R)) else 1 := by
    by_cases hr_i : r = i
    · simp [weylWeightUnit, hr_i]
    · by_cases hr_j : r = j
      · simp [weylWeightUnit, hr_j, hij.symm]
      · simp [weylWeightUnit, hr_i, hr_j]
  have hDiag : (Matrix.diagonal (fun k => (weylWeightUnit i j hij u k : R)) *
      (Equiv.swap i j).permMatrix R) r c =
      if Equiv.swap i j r = c then
        (if r = i then (u : R) else if r = j then (-(↑u⁻¹ : R)) else 1) else 0 := by
    rw [diag_mul_perm_eq, hWeylWeight]
  simp only [hDiag, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hr_i : r = i
  · by_cases hc_j : c = j
    · have hSwap : Equiv.swap i j r = j := by rw [hr_i, Equiv.swap_apply_left]
      grind
    · by_cases hc_i : c = i
      · have hSwap : Equiv.swap i j r = j := by rw [hr_i, Equiv.swap_apply_left]
        grind
      · have hSwap : Equiv.swap i j r = j := by rw [hr_i, Equiv.swap_apply_left]
        grind
  · by_cases hr_j : r = j
    · by_cases hc_i : c = i
      · have hSwap : Equiv.swap i j r = i := by rw [hr_j, Equiv.swap_apply_right]
        grind
      · by_cases hc_j : c = j
        · have hSwap : Equiv.swap i j r = i := by rw [hr_j, Equiv.swap_apply_right]
          grind
        · have hSwap : Equiv.swap i j r = i := by rw [hr_j, Equiv.swap_apply_right]
          grind
    · by_cases hc_eq : c = r
      · have hSwap : Equiv.swap i j r = r :=
          Equiv.swap_apply_of_ne_of_ne hr_i hr_j
        grind
      · have hSwap : Equiv.swap i j r = r :=
          Equiv.swap_apply_of_ne_of_ne hr_i hr_j
        grind

theorem weylGLUnit_eq_monomialMatrixHom (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    weylGLUnit (R := R) i j hij u =
      monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) := by
  apply Units.ext
  calc (weylGLUnit (R := R) i j hij u : Matrix ι ι R)
      = 1 + Matrix.single i j (u : R) + Matrix.single j i (-(↑u⁻¹ : R)) +
        Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) :=
        weylGLUnit_val_eq_sum i j hij u
    _ = (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) : Matrix ι ι R) :=
        (monomialWeyl_val_eq_sum i j hij u).symm

theorem weylGL_eq_monomialMatrixHom (i j : ι) (hij : i ≠ j) :
    weylGL (R := R) i j hij = monomialMatrixHom R ι (weylMonomialBase i j hij) := by
  have h : weylGL (R := R) i j hij = weylGLUnit i j hij 1 := rfl
  rw [h, weylGLUnit_eq_monomialMatrixHom]
  rfl

end WeylRealization

section TorusRealization

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

theorem torusGLUnit_eq_diagonalUnitsHom (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    torusGLUnit (R := R) i j hij u =
      diagonalUnitsHom R ι (torusWeightUnit i j hij u) := by
  apply Units.ext
  have hTorusMono : torusMonomialBaseUnit (R := R) i j hij u =
      weylMonomialBaseUnit i j hij u * weylMonomialBaseUnit i j hij (-1 : Rˣ) :=
    torusMonomialBaseUnit_eq_mul i j hij u
  have hWeyl1 := weylGLUnit_eq_monomialMatrixHom (R := R) i j hij u
  have hWeyl2 := weylGLUnit_eq_monomialMatrixHom (R := R) i j hij (-1 : Rˣ)
  have hMono : monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) =
      weylGLUnit (R := R) i j hij u * weylGLUnit (R := R) i j hij (-1 : Rˣ) := by
    calc monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u)
        = monomialMatrixHom R ι
            (weylMonomialBaseUnit i j hij u * weylMonomialBaseUnit i j hij (-1 : Rˣ)) := by
          rw [← hTorusMono]
      _ = monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) *
          monomialMatrixHom R ι (weylMonomialBaseUnit i j hij (-1 : Rˣ)) := by
          rw [map_mul]
      _ = weylGLUnit (R := R) i j hij u * weylGLUnit (R := R) i j hij (-1 : Rˣ) := by
          rw [← hWeyl1, ← hWeyl2]
  have hDef : torusGLUnit (R := R) i j hij u =
      weylGLUnit i j hij u * weylGLUnit i j hij (-1 : Rˣ) := rfl
  have hMonoEq : monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) =
      torusGLUnit (R := R) i j hij u := by
    rw [hMono, ← hDef]
  have hDiag : (monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) : Matrix ι ι R) =
      Matrix.diagonal (fun k => (torusWeightUnit i j hij u k : R)) := by
    simp [torusMonomialBaseUnit, torusWeightUnit, torusPerm]
  calc (torusGLUnit (R := R) i j hij u : Matrix ι ι R)
      = (monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) : Matrix ι ι R) := by
        rw [hMonoEq]
    _ = Matrix.diagonal (fun k => (torusWeightUnit i j hij u k : R)) := hDiag
    _ = (diagonalUnitsHom R ι (torusWeightUnit i j hij u) : Matrix ι ι R) := rfl

theorem torusGLUnit_eq_monomialMatrixHom (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    torusGLUnit (R := R) i j hij u =
      monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) := by
  have hDiag := torusGLUnit_eq_diagonalUnitsHom (R := R) i j hij u
  have hMonoDiag : monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) =
      diagonalUnitsHom R ι (torusWeightUnit i j hij u) := by
    apply Units.ext
    simp [torusMonomialBaseUnit, torusPerm]
  calc torusGLUnit (R := R) i j hij u
      = diagonalUnitsHom R ι (torusWeightUnit i j hij u) := hDiag
    _ = monomialMatrixHom R ι (torusMonomialBaseUnit i j hij u) := hMonoDiag.symm

theorem torusGL_eq_diagonalUnitsHom (i j : ι) (hij : i ≠ j) :
    torusGL (R := R) i j hij =
      diagonalUnitsHom R ι (torusWeightUnit i j hij 1) := by
  have h : torusGL (R := R) i j hij = torusGLUnit i j hij 1 := rfl
  rw [h, torusGLUnit_eq_diagonalUnitsHom]

theorem torusGL_eq_monomialMatrixHom (i j : ι) (hij : i ≠ j) :
    torusGL (R := R) i j hij =
      monomialMatrixHom R ι (torusMonomialBase i j hij 1) := by
  have h : torusGL (R := R) i j hij = torusGLUnit i j hij 1 := rfl
  rw [h, torusGLUnit_eq_monomialMatrixHom]
  rfl

end TorusRealization

section WeylSLRealization

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

theorem weylSLUnit_eq_monomialSLHom (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    weylSLUnit (R := R) i j hij u =
      monomialSLHom R ι (weylMonomialSLUnit i j hij u) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij u)
      = weylGLUnit (R := R) i j hij u := by
        apply Units.ext
        simp [weylSLUnit, weylGLUnit, Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
    _ = monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) := by
        rw [weylGLUnit_eq_monomialMatrixHom]
    _ = Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι (weylMonomialSLUnit i j hij u)) := by
        simp []

theorem weylSL_eq_monomialSLHom (i j : ι) (hij : i ≠ j) :
    weylSL (R := R) i j hij = monomialSLHom R ι (weylMonomialSL i j hij) := by
  have h : weylSL (R := R) i j hij = weylSLUnit i j hij 1 := rfl
  rw [h, weylSLUnit_eq_monomialSLHom]
  rfl

end WeylSLRealization

section TorusSLRealization

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

theorem torusMonomialSLUnit_eq_weyl_mul (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    torusMonomialSLUnit (R := R) i j hij u =
      weylMonomialSLUnit i j hij u * weylMonomialSLUnit i j hij (-1 : Rˣ) := by
  apply Subtype.ext
  exact torusMonomialBaseUnit_eq_mul i j hij u

theorem torusSLUnit_eq_monomialSLHom (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    torusSLUnit (R := R) i j hij u =
      monomialSLHom R ι (torusMonomialSLUnit i j hij u) := by
  have hWeyl1 := weylSLUnit_eq_monomialSLHom (R := R) i j hij u
  have hWeyl2 := weylSLUnit_eq_monomialSLHom (R := R) i j hij (-1 : Rˣ)
  have hProd : torusMonomialSLUnit (R := R) i j hij u =
      weylMonomialSLUnit i j hij u * weylMonomialSLUnit i j hij (-1 : Rˣ) :=
    torusMonomialSLUnit_eq_weyl_mul i j hij u
  calc torusSLUnit (R := R) i j hij u
      = weylSLUnit i j hij u * weylSLUnit i j hij (-1 : Rˣ) := rfl
    _ = monomialSLHom R ι (weylMonomialSLUnit i j hij u) *
        monomialSLHom R ι (weylMonomialSLUnit i j hij (-1 : Rˣ)) := by rw [hWeyl1, hWeyl2]
    _ = monomialSLHom R ι
          (weylMonomialSLUnit i j hij u * weylMonomialSLUnit i j hij (-1 : Rˣ)) := by
        rw [← map_mul]
    _ = monomialSLHom R ι (torusMonomialSLUnit i j hij u) := by rw [← hProd]

theorem torusSL_eq_monomialSLHom (i j : ι) (hij : i ≠ j) :
    torusSL (R := R) i j hij = monomialSLHom R ι (torusMonomialSL i j hij 1) := by
  have h : torusSL (R := R) i j hij = torusSLUnit i j hij 1 := rfl
  rw [h, torusSLUnit_eq_monomialSLHom]
  rfl

end TorusSLRealization

section FieldTorus

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {F : Type*} [Field F]

theorem torusSLUnit_eq_diag2n (i j : ι) (hij : i ≠ j) (u : Fˣ) :
    torusSLUnit (R := F) i j hij u =
      Matrix.SpecialLinearGroup.diag2n hij (u : F) u.ne_zero := by
  apply Subtype.ext
  have hTorusCoe : (torusSLUnit (R := F) i j hij u : Matrix ι ι F) =
      Matrix.diagonal (fun k => (torusWeightUnit i j hij u k : F)) := by
    have hGL : (Matrix.SpecialLinearGroup.toGL (torusSLUnit i j hij u) : Matrix ι ι F) =
        (torusGLUnit (R := F) i j hij u : Matrix ι ι F) := by
      calc (Matrix.SpecialLinearGroup.toGL (torusSLUnit i j hij u) :
          Matrix ι ι F)
          = (weylSLUnit i j hij u * weylSLUnit i j hij (-1 : Fˣ) :
            Matrix.SpecialLinearGroup ι F).val := rfl
        _ = (weylSLUnit i j hij u : Matrix ι ι F) *
            (weylSLUnit i j hij (-1 : Fˣ) : Matrix ι ι F) := by
            simp [Matrix.SpecialLinearGroup.coe_mul]
        _ = (weylGLUnit (R := F) i j hij u : Matrix ι ι F) *
            (weylGLUnit (R := F) i j hij (-1 : Fˣ) :
              Matrix ι ι F) := by
            simp [weylSLUnit, weylGLUnit,
              Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
        _ = (torusGLUnit (R := F) i j hij u : Matrix ι ι F) := rfl
    have hDiag : (torusGLUnit (R := F) i j hij u : Matrix ι ι F) =
        Matrix.diagonal (fun k => (torusWeightUnit i j hij u k : F)) := by
      have h := torusGLUnit_eq_diagonalUnitsHom (R := F) i j hij u
      have : (torusGLUnit (R := F) i j hij u : Matrix ι ι F) =
          (diagonalUnitsHom F ι (torusWeightUnit i j hij u) : Matrix ι ι F) := by
        rw [h]
      simpa using this
    rw [← hDiag, ← hGL]
    rfl
  have hDiag2n : (Matrix.SpecialLinearGroup.diag2n hij (u : F) u.ne_zero : Matrix ι ι F) =
      Matrix.diagonal (fun k => if k = i then (u : F) else if k = j then (↑u⁻¹ : F) else 1) := by
    simp [Matrix.SpecialLinearGroup.diag2n_coe]
  have hWeight : ∀ k, (torusWeightUnit i j hij u k : F) =
      if k = i then (u : F) else if k = j then (↑u⁻¹ : F) else 1 := by
    intro k
    by_cases hk_i : k = i
    · simp_all [torusWeightUnit]
    · by_cases hk_j : k = j
      · simp [torusWeightUnit, hk_j, hij.symm]
      · simp_all [torusWeightUnit]
  calc (torusSLUnit (R := F) i j hij u : Matrix ι ι F)
      = Matrix.diagonal (fun k => (torusWeightUnit i j hij u k : F)) := hTorusCoe
    _ = Matrix.diagonal (fun k => if k = i then (u : F) else if k = j then (↑u⁻¹ : F) else 1) := by
        congr with k
        rw [hWeight k]
    _ = (Matrix.SpecialLinearGroup.diag2n hij (u : F) u.ne_zero : Matrix ι ι F) := hDiag2n.symm

end FieldTorus

section NaturalityCorollaries

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

theorem weylGLUnit_naturality_via_monomial (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
        (weylGLUnit (R := R) i j hij u) =
      weylGLUnit (R := S) i j hij (Units.map f.toMonoidHom u) := by
  have h1 : Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
      (weylGLUnit (R := R) i j hij u) =
      Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
        (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u)) := by
    exact congrArg (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f)
      (weylGLUnit_eq_monomialMatrixHom (R := R) i j hij u)
  have h2 : Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
      (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u)) =
      monomialMatrixHom S ι
        (PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
          (weylMonomialBaseUnit i j hij u)) := by
    exact monomialMatrixHom_mapRingHom_apply (R := R) (S := S) (f := f)
      (x := weylMonomialBaseUnit i j hij u)
  have h3 : monomialMatrixHom S ι
      (PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
        (weylMonomialBaseUnit i j hij u)) =
      monomialMatrixHom S ι
        (weylMonomialBaseUnit (R := S) i j hij (Units.map f.toMonoidHom u)) := by
    exact congrArg (monomialMatrixHom S ι)
      (weylMonomialBaseUnit_map (f := f) (i := i) (j := j) (hij := hij) (u := u))
  have h4 : monomialMatrixHom S ι
      (weylMonomialBaseUnit (R := S) i j hij (Units.map f.toMonoidHom u)) =
      (weylGLUnit (R := S) i j hij (Units.map f.toMonoidHom u) : GL ι S) := by
    exact (weylGLUnit_eq_monomialMatrixHom (R := S) i j hij (Units.map f.toMonoidHom u)).symm
  calc Matrix.GeneralLinearGroup.mapRingHom f (weylGLUnit i j hij u)
      = Matrix.GeneralLinearGroup.mapRingHom f
          (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u)) := h1
    _ = monomialMatrixHom S ι
          (PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
            (weylMonomialBaseUnit i j hij u)) := h2
    _ = monomialMatrixHom S ι
          (weylMonomialBaseUnit (R := S) i j hij (Units.map f.toMonoidHom u)) := h3
    _ = weylGLUnit (R := S) i j hij (Units.map f.toMonoidHom u) := h4

theorem torusGLUnit_naturality_via_diagonal (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
        (torusGLUnit (R := R) i j hij u) =
      torusGLUnit i j hij (Units.map f.toMonoidHom u) := by
  calc Matrix.GeneralLinearGroup.mapRingHom f (torusGLUnit i j hij u)
      = Matrix.GeneralLinearGroup.mapRingHom f
          (diagonalUnitsHom R ι (torusWeightUnit i j hij u)) := by
        rw [← torusGLUnit_eq_diagonalUnitsHom]
    _ = diagonalUnitsHom S ι (fun k => Units.map f (torusWeightUnit i j hij u k)) := by
        rw [diagonalUnitsHom_mapRingHom]
    _ = diagonalUnitsHom S ι (torusWeightUnit i j hij (Units.map f.toMonoidHom u)) := by
        congr with k
        by_cases hk_i : k = i
        · simp [hk_i, torusWeightUnit]
        · by_cases hk_j : k = j
          · simp [torusWeightUnit, hk_j, hij.symm, map_inv]
          · simp_all [torusWeightUnit]
    _ = torusGLUnit (R := S) i j hij (Units.map f.toMonoidHom u) := by
        rw [← torusGLUnit_eq_diagonalUnitsHom (R := S)]

theorem weylSLUnit_naturality_via_monomial (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup.map f (weylSLUnit (R := R) i j hij u) =
      weylSLUnit (R := S) i j hij (Units.map f.toMonoidHom u) := by
  calc Matrix.SpecialLinearGroup.map f (weylSLUnit i j hij u)
      = Matrix.SpecialLinearGroup.map f
          (monomialSLHom R ι (weylMonomialSLUnit i j hij u)) := by
        rw [← weylSLUnit_eq_monomialSLHom]
    _ = monomialSLHom S ι
          (monomialSLMap R S ι f (weylMonomialSLUnit i j hij u)) := by
        apply Subtype.ext
        simp
    _ = monomialSLHom S ι
          (weylMonomialSLUnit (R := S) i j hij (Units.map f.toMonoidHom u)) := by
        rw [weylMonomialSLUnit_map f i j hij u]
    _ = weylSLUnit (R := S) i j hij (Units.map f.toMonoidHom u) := by
        rw [← weylSLUnit_eq_monomialSLHom (R := S)]

end NaturalityCorollaries

section RankOneGL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

private lemma torusGLUnit_inv_eq (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    ((torusGLUnit i j hij v)⁻¹ : GL ι R) = torusGLUnit i j hij v⁻¹ := by
  have h1 := torusGLUnit_eq_diagonalUnitsHom (R := R) i j hij v
  have h2 := torusGLUnit_eq_diagonalUnitsHom (R := R) i j hij v⁻¹
  calc ((torusGLUnit i j hij v)⁻¹ : GL ι R)
      = (diagonalUnitsHom R ι (torusWeightUnit i j hij v))⁻¹ := by
        rw [h1]
    _ = diagonalUnitsHom R ι ((torusWeightUnit i j hij v)⁻¹) := by
        rw [← map_inv]
    _ = diagonalUnitsHom R ι (torusWeightUnit i j hij v⁻¹) := by
        congr with k
        by_cases hk_i : k = i
        · simp [torusWeightUnit, hk_i]
        · by_cases hk_j : k = j
          · simp_all [torusWeightUnit]
          · simp [torusWeightUnit, hk_i, hk_j]
    _ = torusGLUnit i j hij v⁻¹ := by rw [← h2]

omit [Fintype ι] in
private lemma diag_torus_decomp (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    Matrix.diagonal (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) =
      (1 : Matrix ι ι R) + Matrix.single i i ((v : R) - 1) +
        Matrix.single j j ((↑v⁻¹ : R) - 1) := by
  ext r c
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.diagonal_apply]
  by_cases hrc : r = c
  · subst hrc
    by_cases hi : r = i
    · have hj : r ≠ j := by intro h; exact hij (hi.symm.trans h)
      grind
    · by_cases hj : r = j
      · grind
      · grind
  · grind

private lemma diag_mul_single_eq (i j : ι) (_hij : i ≠ j) (v : Rˣ) :
    Matrix.diagonal (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) *
        Matrix.single i j (-(↑v⁻¹ : R)) =
      Matrix.single i j (-1 : R) := by
  have hv : (v : R) * (-(↑v⁻¹ : R)) = -1 := by
    have h1 : (v : R) * (↑v⁻¹ : R) = 1 := by
      calc (v : R) * (↑v⁻¹ : R) = ((v * v⁻¹ : Rˣ) : R) := by rw [Units.val_mul]
        _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
        _ = 1 := rfl
    calc (v : R) * (-(↑v⁻¹ : R)) = -((v : R) * (↑v⁻¹ : R)) := by rw [mul_neg]
      _ = -1 := by rw [h1]
  ext r c
  simp only [Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hr_i : r = i
  · by_cases hc_j : c = j
    · grind
    · grind
  · grind

private lemma single_mul_diag_eq (i j : ι) (_hij : i ≠ j) (v : Rˣ) :
    Matrix.single j i (↑v⁻¹ : R) *
        Matrix.diagonal
          (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) =
      Matrix.single j i (1 : R) := by
  have hv : (↑v⁻¹ : R) * (v : R) = 1 := by
    calc (↑v⁻¹ : R) * (v : R) = ((v⁻¹ * v : Rˣ) : R) := by rw [Units.val_mul]
      _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
      _ = 1 := rfl
  ext r c
  simp only [Matrix.mul_diagonal, Matrix.single_apply]
  by_cases hr_j : r = j
  · by_cases hc_i : c = i
    · grind
    · grind
  · grind

private lemma single_mul_diag_left_eq (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    Matrix.single i j (-(↑v⁻¹ : R)) *
        Matrix.diagonal
          (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) =
      Matrix.single i j (-1 : R) := by
  have hv : (-(↑v⁻¹ : R)) * (v : R) = -1 := by
    have h1 : (↑v⁻¹ : R) * (v : R) = 1 := by
      calc (↑v⁻¹ : R) * (v : R) = ((v⁻¹ * v : Rˣ) : R) := by rw [Units.val_mul]
        _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
        _ = 1 := rfl
    calc (-(↑v⁻¹ : R)) * (v : R) = -((↑v⁻¹ : R) * (v : R)) := by rw [neg_mul]
      _ = -1 := by rw [h1]
  ext r c
  simp only [Matrix.mul_diagonal, Matrix.single_apply]
  by_cases hr_i : r = i
  · by_cases hc_j : c = j
    · grind
    · grind
  · grind

private lemma diag_mul_single_left_eq (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    Matrix.diagonal (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) *
        Matrix.single j i (↑v⁻¹ : R) =
      Matrix.single j i (1 : R) := by
  have hv : (v : R) * (↑v⁻¹ : R) = 1 := by
    calc (v : R) * (↑v⁻¹ : R) = ((v * v⁻¹ : Rˣ) : R) := by rw [Units.val_mul]
      _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
      _ = 1 := rfl
  ext r c
  simp only [Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hr_j : r = j
  · by_cases hc_i : c = i
    · grind
    · grind
  · grind

theorem rankOneGL_right (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    elementary i j hij (v : R) * weylGLUnit i j hij (-1 : Rˣ) =
      elementary j i hij.symm (↑v⁻¹ : R) * torusGLUnit i j hij v *
        elementary i j hij (-(↑v⁻¹ : R)) := by
  apply Units.ext
  have hW : (weylGLUnit i j hij (-1 : Rˣ) : Matrix ι ι R) =
      1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
        Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
    have h := weylGLUnit_val_eq_sum (R := R) i j hij (-1 : Rˣ)
    have hNegOneInv : ((-1 : Rˣ)⁻¹ : Rˣ) = -1 := by
      apply Units.ext
      simp
    have h1 : (↑(-1 : Rˣ) : R) = (-1 : R) := rfl
    have h2 : (-(↑(-1 : Rˣ)⁻¹ : R)) = (1 : R) := by
      have : (↑(-1 : Rˣ)⁻¹ : R) = (-1 : R) := by
        calc (↑(-1 : Rˣ)⁻¹ : R) = (↑((-1 : Rˣ)⁻¹) : R) := rfl
          _ = (↑(-1 : Rˣ) : R) := by rw [hNegOneInv]
          _ = (-1 : R) := rfl
      rw [this, neg_neg]
    calc (weylGLUnit i j hij (-1 : Rˣ) : Matrix ι ι R)
        = 1 + Matrix.single i j (↑(-1 : Rˣ) : R) +
            Matrix.single j i (-(↑(-1 : Rˣ)⁻¹ : R)) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := h
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
          rw [h1, h2]
  have hT :
      (torusGLUnit i j hij v : Matrix ι ι R) =
        Matrix.diagonal
          (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) := by
    have hDiag :
        (torusGLUnit i j hij v : Matrix ι ι R) =
          Matrix.diagonal (fun k => (torusWeightUnit i j hij v k : R)) := by
      have h := torusGLUnit_eq_diagonalUnitsHom (R := R) i j hij v
      calc (torusGLUnit i j hij v : Matrix ι ι R)
          = (diagonalUnitsHom R ι (torusWeightUnit i j hij v) :
            Matrix ι ι R) := by rw [h]
        _ = _ := rfl
    calc (torusGLUnit i j hij v : Matrix ι ι R)
        = Matrix.diagonal (fun k => (torusWeightUnit i j hij v k : R)) :=
          hDiag
      _ = Matrix.diagonal
          (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) := by
            congr with k
            by_cases hk_i : k = i
            · simp [torusWeightUnit, hk_i]
            · by_cases hk_j : k = j
              · simp_all [torusWeightUnit]
              · simp [torusWeightUnit, hk_i, hk_j]
  have hDS := diag_mul_single_eq i j hij v
  have hSD := single_mul_diag_eq i j hij v
  have hDiagDecomp := diag_torus_decomp i j hij v
  have hIntermediate :
      (1 + Matrix.single i j (v : R)) *
          (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) =
        1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R) := by
    have h1 :
        Matrix.single i j (v : R) * Matrix.single i j (-1 : R) = 0 := by
      simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    have h2 :
        Matrix.single i j (v : R) * Matrix.single j i (1 : R) =
          Matrix.single i i (v : R) := by
      simp [Matrix.single_mul_single_same]
    have h3 :
        Matrix.single i j (v : R) * Matrix.single i i (-1 : R) = 0 := by
      simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    have h4 :
        Matrix.single i j (v : R) * Matrix.single j j (-1 : R) =
          Matrix.single i j (-(v : R)) := by
      calc Matrix.single i j (v : R) * Matrix.single j j (-1 : R)
          = Matrix.single i j ((v : R) * (-1 : R)) := by
            simp [Matrix.single_mul_single_same]
        _ = Matrix.single i j (-(v : R)) := by rw [mul_neg_one]
    calc (1 + Matrix.single i j (v : R)) *
          (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R))
        = 1 * (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) +
          Matrix.single i j (v : R) *
            (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
              Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) := by
          rw [add_mul]
      _ = (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) +
          (Matrix.single i j (v : R) + 0 + Matrix.single i i (v : R) + 0 +
            Matrix.single i j (-(v : R))) := by
          simp only [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, h1, h2, h3, h4]
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) +
          Matrix.single i i (v : R) + Matrix.single i j (v : R) +
          Matrix.single i j (-(v : R)) := by abel
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          (Matrix.single i i (-1 : R) + Matrix.single i i (v : R)) +
          Matrix.single j j (-1 : R) +
          (Matrix.single i j (v : R) + Matrix.single i j (-(v : R))) := by abel
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R) := by
          have hAdd1 : Matrix.single i i (-1 : R) + Matrix.single i i (v : R) =
              Matrix.single i i ((v : R) - 1) := by
            rw [← Matrix.single_add, show -1 + (v : R) = (v : R) - 1 from by abel]
          have hAdd2 : Matrix.single i j (v : R) + Matrix.single i j (-(v : R)) = 0 := by
            rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
          rw [hAdd1, hAdd2, add_zero]
  have hRHS_eq :
      (1 + Matrix.single j i (↑v⁻¹ : R)) *
          Matrix.diagonal
            (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) *
          (1 + Matrix.single i j (-(↑v⁻¹ : R))) =
        1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R) := by
    calc (1 + Matrix.single j i (↑v⁻¹ : R)) *
          Matrix.diagonal
            (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) *
          (1 + Matrix.single i j (-(↑v⁻¹ : R)))
        = ((1 + Matrix.single j i (↑v⁻¹ : R)) *
            Matrix.diagonal
              (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1)) *
          (1 + Matrix.single i j (-(↑v⁻¹ : R))) := by rw [mul_assoc]
      _ = (Matrix.diagonal
              (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) +
            Matrix.single j i (1 : R)) *
          (1 + Matrix.single i j (-(↑v⁻¹ : R))) := by rw [add_mul, Matrix.one_mul, hSD]
      _ = Matrix.diagonal
            (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) *
            (1 + Matrix.single i j (-(↑v⁻¹ : R))) +
          Matrix.single j i (1 : R) * (1 + Matrix.single i j (-(↑v⁻¹ : R))) := by
          rw [add_mul]
      _ = Matrix.diagonal
            (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) +
          Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single j i (1 : R) * Matrix.single i j (-(↑v⁻¹ : R)) := by
          simp only [Matrix.mul_add, Matrix.mul_one, hDS]
          abel
      _ = Matrix.diagonal
            (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) +
          Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single j j (-(↑v⁻¹ : R)) := by
          rw [Matrix.single_mul_single_same, one_mul]
      _ = (1 + Matrix.single i i ((v : R) - 1) + Matrix.single j j ((↑v⁻¹ : R) - 1)) +
          Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single j j (-(↑v⁻¹ : R)) := by rw [hDiagDecomp]
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i ((v : R) - 1) +
          (Matrix.single j j ((↑v⁻¹ : R) - 1) + Matrix.single j j (-(↑v⁻¹ : R))) := by
          abel
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R) := by
          have : Matrix.single j j ((↑v⁻¹ : R) - 1) + Matrix.single j j (-(↑v⁻¹ : R)) =
              Matrix.single j j (-1 : R) := by
            rw [← Matrix.single_add, show (↑v⁻¹ : R) - 1 + (-(↑v⁻¹ : R)) = -1 from by abel]
          rw [this]
  calc (↑(elementary i j hij (v : R) * weylGLUnit i j hij (-1 : Rˣ)) :
      Matrix ι ι R)
      = (1 + Matrix.single i j (v : R)) *
        (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) := by
        simp [coe_elementary, hW]
    _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
        Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R) := hIntermediate
    _ = (↑(elementary j i hij.symm (↑v⁻¹ : R) * torusGLUnit i j hij v *
        elementary i j hij (-(↑v⁻¹ : R))) : Matrix ι ι R) := by
        calc 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
              Matrix.single i i ((v : R) - 1) + Matrix.single j j (-1 : R)
            = (1 + Matrix.single j i (↑v⁻¹ : R)) *
                Matrix.diagonal
                  (fun k => if k = i then (v : R) else if k = j then (↑v⁻¹ : R) else 1) *
                (1 + Matrix.single i j (-(↑v⁻¹ : R))) := by
              rw [← hRHS_eq]
            _ = (↑(elementary j i hij.symm (↑v⁻¹ : R) * torusGLUnit i j hij v *
                elementary i j hij (-(↑v⁻¹ : R))) : Matrix ι ι R) := by
              simp [coe_elementary, hT]

theorem rankOneGL_left (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    weylGLUnit i j hij (-1 : Rˣ) * elementary i j hij (v : R) =
      elementary i j hij (-(↑v⁻¹ : R)) * (torusGLUnit i j hij v)⁻¹ *
        elementary j i hij.symm (↑v⁻¹ : R) := by
  apply Units.ext
  have hW : (weylGLUnit i j hij (-1 : Rˣ) : Matrix ι ι R) =
      1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
        Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
    have h := weylGLUnit_val_eq_sum (R := R) i j hij (-1 : Rˣ)
    have hNegOneInv : ((-1 : Rˣ)⁻¹ : Rˣ) = -1 := by
      apply Units.ext
      simp
    have h1 : (↑(-1 : Rˣ) : R) = (-1 : R) := rfl
    have h2 : (-(↑(-1 : Rˣ)⁻¹ : R)) = (1 : R) := by
      have : (↑(-1 : Rˣ)⁻¹ : R) = (-1 : R) := by
        calc (↑(-1 : Rˣ)⁻¹ : R) = (↑((-1 : Rˣ)⁻¹) : R) := rfl
          _ = (↑(-1 : Rˣ) : R) := by rw [hNegOneInv]
          _ = (-1 : R) := rfl
      rw [this, neg_neg]
    calc (weylGLUnit i j hij (-1 : Rˣ) : Matrix ι ι R)
        = 1 + Matrix.single i j (↑(-1 : Rˣ) : R) +
            Matrix.single j i (-(↑(-1 : Rˣ)⁻¹ : R)) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := h
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) := by
          rw [h1, h2]
  have hTinv : ((torusGLUnit i j hij v)⁻¹ : GL ι R) =
      torusGLUnit i j hij v⁻¹ := torusGLUnit_inv_eq i j hij v
  have hTvalInv :
      (((torusGLUnit i j hij v)⁻¹ : GL ι R) : Matrix ι ι R) =
        Matrix.diagonal
          (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) := by
    calc (((torusGLUnit i j hij v)⁻¹ : GL ι R) : Matrix ι ι R)
        = (torusGLUnit i j hij v⁻¹ : Matrix ι ι R) := by
          rw [hTinv]
      _ = Matrix.diagonal
          (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) := by
            have hDiag :
                (torusGLUnit i j hij v⁻¹ : Matrix ι ι R) =
                  Matrix.diagonal (fun k => (torusWeightUnit i j hij v⁻¹ k : R)) := by
              have h := torusGLUnit_eq_diagonalUnitsHom (R := R) i j hij v⁻¹
              calc (torusGLUnit i j hij v⁻¹ : Matrix ι ι R)
                  = (diagonalUnitsHom R ι (torusWeightUnit i j hij v⁻¹) :
                    Matrix ι ι R) := by rw [h]
                _ = _ := rfl
            calc (torusGLUnit i j hij v⁻¹ : Matrix ι ι R)
                = Matrix.diagonal (fun k => (torusWeightUnit i j hij v⁻¹ k : R)) :=
                  hDiag
              _ = Matrix.diagonal
                  (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) := by
                    congr with k
                    by_cases hk_i : k = i
                    · simp_all [torusWeightUnit]
                    · by_cases hk_j : k = j
                      · simp_all [torusWeightUnit]
                      · simp_all [torusWeightUnit]
  have hDS2 := single_mul_diag_left_eq i j hij v
  have hSD2 := diag_mul_single_left_eq i j hij v
  have hDiagDecompInv :
      Matrix.diagonal
          (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) =
        (1 : Matrix ι ι R) + Matrix.single i i ((↑v⁻¹ : R) - 1) +
          Matrix.single j j ((v : R) - 1) := by
    have h := diag_torus_decomp i j hij v⁻¹
    have hSwap : (↑v⁻¹⁻¹ : R) = (v : R) := by
      calc (↑v⁻¹⁻¹ : R) = (↑(v⁻¹⁻¹ : Rˣ) : R) := rfl
        _ = (↑v : R) := by rw [inv_inv]
    simp only [hSwap] at h
    exact h
  have hIntermediateLeft :
      (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) *
        (1 + Matrix.single i j (v : R)) =
        1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by
    have h1 :
        Matrix.single i j (-1 : R) * Matrix.single i j (v : R) = 0 := by
      simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    have h2 :
        Matrix.single j i (1 : R) * Matrix.single i j (v : R) =
          Matrix.single j j (v : R) := by
      simp [Matrix.single_mul_single_same]
    have h3 :
        Matrix.single i i (-1 : R) * Matrix.single i j (v : R) =
          Matrix.single i j (-(v : R)) := by
      calc Matrix.single i i (-1 : R) * Matrix.single i j (v : R)
          = Matrix.single i j ((-1 : R) * (v : R)) := by
            simp [Matrix.single_mul_single_same]
        _ = Matrix.single i j (-(v : R)) := by rw [neg_one_mul]
    have h4 :
        Matrix.single j j (-1 : R) * Matrix.single i j (v : R) = 0 := by
      simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    calc (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) *
        (1 + Matrix.single i j (v : R))
        = (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) * 1 +
          (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) *
            Matrix.single i j (v : R) := by rw [mul_add]
      _ = (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
            Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) +
          (Matrix.single i j (v : R) + 0 + Matrix.single j j (v : R) +
            Matrix.single i j (-(v : R)) + 0) := by
          simp [h1, h2, h3, h4, Matrix.add_mul]
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R) +
          Matrix.single j j (v : R) + Matrix.single i j (v : R) +
          Matrix.single i j (-(v : R)) := by abel
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) +
          (Matrix.single j j (-1 : R) + Matrix.single j j (v : R)) +
          (Matrix.single i j (v : R) + Matrix.single i j (-(v : R))) := by abel
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by
          have hAdd1 : Matrix.single j j (-1 : R) + Matrix.single j j (v : R) =
              Matrix.single j j ((v : R) - 1) := by
            rw [← Matrix.single_add, show -1 + (v : R) = (v : R) - 1 from by abel]
          have hAdd2 : Matrix.single i j (v : R) + Matrix.single i j (-(v : R)) = 0 := by
            rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
          rw [hAdd1, hAdd2, add_zero]
  have hRHSLeft :
      (1 + Matrix.single i j (-(↑v⁻¹ : R))) *
          Matrix.diagonal
            (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) *
          (1 + Matrix.single j i (↑v⁻¹ : R)) =
        1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by
    calc (1 + Matrix.single i j (-(↑v⁻¹ : R))) *
          Matrix.diagonal
            (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) *
          (1 + Matrix.single j i (↑v⁻¹ : R))
        = ((1 + Matrix.single i j (-(↑v⁻¹ : R))) *
            Matrix.diagonal
              (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1)) *
          (1 + Matrix.single j i (↑v⁻¹ : R)) := by rw [mul_assoc]
      _ = (Matrix.diagonal
              (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) +
            Matrix.single i j (-1 : R)) *
          (1 + Matrix.single j i (↑v⁻¹ : R)) := by
          rw [add_mul, Matrix.one_mul, hDS2]
      _ = Matrix.diagonal
            (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) *
            (1 + Matrix.single j i (↑v⁻¹ : R)) +
          Matrix.single i j (-1 : R) * (1 + Matrix.single j i (↑v⁻¹ : R)) := by
          rw [add_mul]
      _ = Matrix.diagonal
            (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) +
          Matrix.single j i (1 : R) + Matrix.single i j (-1 : R) +
          Matrix.single i i (-(↑v⁻¹ : R)) := by
          simp [Matrix.mul_add, hSD2, Matrix.single_mul_single_same]
          abel
      _ = Matrix.diagonal
            (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) +
          Matrix.single j i (1 : R) + Matrix.single i j (-1 : R) +
          Matrix.single i i (-(↑v⁻¹ : R)) := rfl
      _ = (1 + Matrix.single i i ((↑v⁻¹ : R) - 1) + Matrix.single j j ((v : R) - 1)) +
          Matrix.single j i (1 : R) + Matrix.single i j (-1 : R) +
          Matrix.single i i (-(↑v⁻¹ : R)) := by rw [hDiagDecompInv]
      _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by
          have h : Matrix.single i i ((↑v⁻¹ : R) - 1) + Matrix.single i i (-(↑v⁻¹ : R)) =
              Matrix.single i i (-1 : R) := by
            rw [← Matrix.single_add, show (↑v⁻¹ : R) - 1 + (-(↑v⁻¹ : R)) = -1 from by abel]
          calc 1 + Matrix.single i i ((↑v⁻¹ : R) - 1) + Matrix.single j j ((v : R) - 1) +
                Matrix.single j i (1 : R) + Matrix.single i j (-1 : R) +
                Matrix.single i i (-(↑v⁻¹ : R))
              = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
                (Matrix.single i i ((↑v⁻¹ : R) - 1) + Matrix.single i i (-(↑v⁻¹ : R))) +
                Matrix.single j j ((v : R) - 1) := by abel
            _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
                Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by rw [h]
  calc (↑(weylGLUnit i j hij (-1 : Rˣ) * elementary i j hij (v : R)) :
      Matrix ι ι R)
      = (1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
          Matrix.single i i (-1 : R) + Matrix.single j j (-1 : R)) *
        (1 + Matrix.single i j (v : R)) := by
        simp [coe_elementary, hW]
    _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
        Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := hIntermediateLeft
    _ = (↑(elementary i j hij (-(↑v⁻¹ : R)) * (torusGLUnit i j hij v)⁻¹ *
        elementary j i hij.symm (↑v⁻¹ : R)) : Matrix ι ι R) := by
        have hEq : (↑(elementary i j hij (-(↑v⁻¹ : R)) * (torusGLUnit i j hij v)⁻¹ *
            elementary j i hij.symm (↑v⁻¹ : R)) : Matrix ι ι R) =
            1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
              Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) := by
          calc (↑(elementary i j hij (-(↑v⁻¹ : R)) * (torusGLUnit i j hij v)⁻¹ *
              elementary j i hij.symm (↑v⁻¹ : R)) : Matrix ι ι R)
              = (1 + Matrix.single i j (-(↑v⁻¹ : R))) *
                  Matrix.diagonal
                    (fun k => if k = i then (↑v⁻¹ : R) else if k = j then (v : R) else 1) *
                  (1 + Matrix.single j i (↑v⁻¹ : R)) := by
                simp [coe_elementary, hTvalInv]
            _ = 1 + Matrix.single i j (-1 : R) + Matrix.single j i (1 : R) +
                  Matrix.single i i (-1 : R) + Matrix.single j j ((v : R) - 1) :=
                hRHSLeft
        exact hEq.symm

end RankOneGL


section RankOneSL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

theorem rankOneSL_right (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    Matrix.SpecialLinearGroup.transvection hij (v : R) *
        weylSLUnit i j hij (-1 : Rˣ) =
      Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R) *
        torusSLUnit i j hij v *
        Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R)) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hGL := rankOneGL_right (R := R) i j hij v
  calc Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (v : R) *
          weylSLUnit i j hij (-1 : Rˣ))
      = Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (v : R)) *
        Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij (-1 : Rˣ)) := by
          rw [map_mul]
    _ = (elementary i j hij (v : R) : GL ι R) *
        (weylGLUnit i j hij (-1 : Rˣ) : GL ι R) := by
          have hTrans : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij (v : R)) =
              (elementary i j hij (v : R) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hW : (Matrix.SpecialLinearGroup.toGL
              (weylSLUnit i j hij (-1 : Rˣ)) : GL ι R) =
              weylGLUnit i j hij (-1 : Rˣ) := by
            apply Units.ext
            simp [weylSLUnit, weylGLUnit,
              Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          rw [hTrans, hW]
    _ = (elementary j i hij.symm (↑v⁻¹ : R) : GL ι R) *
        (torusGLUnit i j hij v : GL ι R) *
        (elementary i j hij (-(↑v⁻¹ : R)) : GL ι R) := by
          rw [hGL]
    _ = Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R) *
          torusSLUnit i j hij v *
          Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R))) := by
          have hTrans1 : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R)) =
              (elementary j i hij.symm (↑v⁻¹ : R) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hTrans2 : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R))) =
              (elementary i j hij (-(↑v⁻¹ : R)) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hT : (Matrix.SpecialLinearGroup.toGL
              (torusSLUnit i j hij v) : GL ι R) =
              torusGLUnit i j hij v := by
            apply Units.ext
            simp [torusSLUnit, torusGLUnit, weylSLUnit, weylGLUnit,
              Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          simp [hTrans1, hTrans2, hT, map_mul]

theorem rankOneSL_left (i j : ι) (hij : i ≠ j) (v : Rˣ) :
    weylSLUnit i j hij (-1 : Rˣ) *
        Matrix.SpecialLinearGroup.transvection hij (v : R) =
      Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R)) *
        (torusSLUnit i j hij v)⁻¹ *
        Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hGL := rankOneGL_left (R := R) i j hij v
  calc Matrix.SpecialLinearGroup.toGL
        (weylSLUnit i j hij (-1 : Rˣ) *
          Matrix.SpecialLinearGroup.transvection hij (v : R))
      = Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij (-1 : Rˣ)) *
        Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (v : R)) := by
          rw [map_mul]
    _ = (weylGLUnit i j hij (-1 : Rˣ) : GL ι R) *
        (elementary i j hij (v : R) : GL ι R) := by
          have hTrans : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij (v : R)) =
              (elementary i j hij (v : R) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hW : (Matrix.SpecialLinearGroup.toGL
              (weylSLUnit i j hij (-1 : Rˣ)) : GL ι R) =
              weylGLUnit i j hij (-1 : Rˣ) := by
            apply Units.ext
            simp [weylSLUnit, weylGLUnit,
              Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          rw [hW, hTrans]
    _ = (elementary i j hij (-(↑v⁻¹ : R)) : GL ι R) *
        ((torusGLUnit i j hij v)⁻¹ : GL ι R) *
        (elementary j i hij.symm (↑v⁻¹ : R) : GL ι R) := by
          rw [hGL]
    _ = Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R)) *
          (torusSLUnit i j hij v)⁻¹ *
          Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R)) := by
          have hTrans1 : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij (-(↑v⁻¹ : R))) =
              (elementary i j hij (-(↑v⁻¹ : R)) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hTrans2 : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij.symm (↑v⁻¹ : R)) =
              (elementary j i hij.symm (↑v⁻¹ : R) : GL ι R) := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          have hT : (Matrix.SpecialLinearGroup.toGL
              (torusSLUnit i j hij v) : GL ι R) =
              torusGLUnit i j hij v := by
            apply Units.ext
            simp [torusSLUnit, torusGLUnit, weylSLUnit, weylGLUnit,
              Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]
          simp [hTrans1, hTrans2, hT, map_inv, map_mul]

end RankOneSL

section TorusInverse

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

omit [Fintype ι] in
theorem torusWeightUnit_inv_eq (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (torusWeightUnit (R := R) i j hij u)⁻¹ = torusWeightUnit (R := R) i j hij u⁻¹ := by
  ext k
  simp only [Pi.inv_def]
  by_cases hk_i : k = i
  · simp [hk_i, torusWeightUnit]
  · by_cases hk_j : k = j
    · simp [hk_j, hij.symm, torusWeightUnit]
    · simp [hk_i, hk_j, torusWeightUnit]

omit [Fintype ι] in
theorem torusMonomialBaseUnit_inv_eq (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (torusMonomialBaseUnit (R := R) i j hij u)⁻¹ =
      torusMonomialBaseUnit (R := R) i j hij u⁻¹ := by
  have hProd : torusMonomialBaseUnit (R := R) i j hij u *
      torusMonomialBaseUnit (R := R) i j hij u⁻¹ = 1 := by
    apply SemidirectProduct.ext
    · ext k
      simp only [SemidirectProduct.mul_left, torusMonomialBaseUnit, torusPerm,
        tupleActionHom_apply, permute_apply, Pi.mul_apply, torusWeightUnit]
      by_cases hk_i : k = i
      · simp [hk_i, mul_inv_cancel]
      · by_cases hk_j : k = j
        · simp [hk_j, hij.symm, inv_mul_cancel]
        · simp [hk_i, hk_j]
    · simp [torusMonomialBaseUnit, torusPerm]
  exact inv_eq_of_mul_eq_one_right hProd

theorem torusMonomialSLUnit_inv_eq (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (torusMonomialSLUnit (R := R) i j hij u)⁻¹ =
      torusMonomialSLUnit (R := R) i j hij u⁻¹ := by
  apply Subtype.ext
  exact torusMonomialBaseUnit_inv_eq i j hij u

theorem torusSLUnit_inv_eq (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (torusSLUnit (R := R) i j hij u)⁻¹ = torusSLUnit (R := R) i j hij u⁻¹ := by
  calc (torusSLUnit (R := R) i j hij u)⁻¹
      = (monomialSLHom R ι (torusMonomialSLUnit i j hij u))⁻¹ := by
        rw [← torusSLUnit_eq_monomialSLHom]
    _ = monomialSLHom R ι (torusMonomialSLUnit i j hij u)⁻¹ := by
        rw [← map_inv]
    _ = monomialSLHom R ι (torusMonomialSLUnit i j hij u⁻¹) := by
        rw [torusMonomialSLUnit_inv_eq]
    _ = torusSLUnit (R := R) i j hij u⁻¹ := by
        rw [torusSLUnit_eq_monomialSLHom]

end TorusInverse

section TorusBruhatMiddle

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

theorem bruhatMiddle_torusSLUnit (i j : ι) (hij : i ≠ j) (u : Fˣ) :
    bruhatMiddle (torusSLUnit (R := F) i j hij u) =
      torusMonomialSLUnit (R := F) i j hij u := by
  calc bruhatMiddle (torusSLUnit (R := F) i j hij u)
      = bruhatMiddle (monomialSLHom F ι (torusMonomialSLUnit i j hij u)) := by
        rw [torusSLUnit_eq_monomialSLHom]
    _ = torusMonomialSLUnit (R := F) i j hij u :=
        bruhatMiddle_monomialSLHom (torusMonomialSLUnit i j hij u)

end TorusBruhatMiddle

end Matrix.GeneralLinearGroup
