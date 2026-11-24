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
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization
/-! # Equal-index factorization for `GL` over a field -/
@[expose] public section
namespace Matrix.GeneralLinearGroup
open Matrix
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {F : Type*} [Field F]
private lemma s_mul_d (i j : ι) (a : F) (d : ι → F) :
    single i j a * diagonal d = single i j (a * d j) := by
  ext r c
  simp only [mul_diagonal, single_apply]
  by_cases hr : i = r
  · subst hr
    by_cases hc : j = c
    · subst hc; simp
    · simp [hc]
  · simp [hr]
private lemma d_mul_s (i j : ι) (a : F) (d : ι → F) :
    diagonal d * single i j a = single i j (d i * a) := by
  ext r c
  simp only [diagonal_mul, single_apply]
  by_cases hr : i = r
  · subst hr
    by_cases hc : j = c
    · subst hc; simp
    · simp [hc]
  · simp [hr]
omit [Fintype ι] in
private lemma diag_one_two (i j : ι) (hij : i ≠ j) (p q : F) :
    diagonal (fun k => if k = i then p else if k = j then q else (1 : F)) =
      (1 : Matrix ι ι F) + single i i (p - 1) + single j j (q - 1) := by
  ext r c
  simp only [diagonal_apply]
  by_cases hrc : r = c
  · subst hrc
    by_cases hi : r = i
    · subst hi
      simp [hij.symm]
    · by_cases hj : r = j
      · subst hj
        simp [hi, hij]
      · simp [hi, hj, Ne.symm hi, Ne.symm hj]
  · have hi : ¬(i = r ∧ i = c) := fun ⟨hr, hc⟩ => hrc (hr.symm.trans hc)
    have hj : ¬(j = r ∧ j = c) := fun ⟨hr, hc⟩ => hrc (hr.symm.trans hc)
    simp [hi, hj, hrc]
/-- Row-times-column equal-index factorization.
If `u = 1 + a * b ≠ 0` then `E_{ji}(b) E_{ij}(a) = E_{ij}(a/u) h_{ij}(u)⁻¹ E_{ji}(b/u)`.
Char 2 valid; uses diagonal form of `torusGLUnit`. -/
theorem equalIndexFactorization_row_col (i j : ι) (hij : i ≠ j)
    (a b : F) (hu : 1 + a * b ≠ 0) :
    elementary j i hij.symm b * elementary i j hij a =
      elementary i j hij (a / (1 + a * b)) *
        (torusGLUnit i j hij (Units.mk0 (1 + a * b) hu))⁻¹ *
        elementary j i hij.symm (b / (1 + a * b)) := by
  set u := 1 + a * b
  have hu0 : u ≠ 0 := hu
  set v := Units.mk0 u hu0
  have hv : (v : F) = u := Units.val_mk0 hu0
  have hvI : (↑v⁻¹ : F) = u⁻¹ := by
    have hmul : (v : F) * (↑v⁻¹ : F) = 1 := by
      calc (v : F) * (↑v⁻¹ : F) = ((v * v⁻¹ : Fˣ) : F) := by
            rw [Units.val_mul]
        _ = ((1 : Fˣ) : F) := by rw [mul_inv_cancel]
        _ = 1 := rfl
    rw [hv] at hmul
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  have hT : torusGLUnit i j hij v =
      diagonalUnitsHom F ι (torusWeightUnit i j hij v) :=
    torusGLUnit_eq_diagonalUnitsHom i j hij v
  have hTI : (torusGLUnit i j hij v)⁻¹ =
      diagonalUnitsHom F ι ((torusWeightUnit i j hij v)⁻¹) := by
    rw [hT, ← map_inv]
  have hDv : ((torusGLUnit i j hij v)⁻¹ : GL ι F).val =
      diagonal (fun k => if k = i then u⁻¹ else if k = j then u else 1) := by
    rw [hTI]
    ext r c
    simp only [coe_diagonalUnitsHom, diagonal_apply, Pi.inv_def]
    by_cases hrc : r = c
    · subst hrc
      by_cases hi : r = i
      · subst hi
        simp only [torusWeightUnit, ite_true, hvI]
      · by_cases hj : r = j
        · subst hj
          simp [hi, torusWeightUnit, hv]
        · simp [hi, hj, torusWeightUnit]
    · simp [hrc]
  set d : ι → F := fun k => if k = i then u⁻¹ else if k = j then u else 1
  have hd_j : d j = u := by simp [d, hij.symm]
  have hD : diagonal d =
      (1 : Matrix ι ι F) + single i i (u⁻¹ - 1) + single j j (u - 1) :=
    diag_one_two i j hij u⁻¹ u
  have hL : ((elementary j i hij.symm b * elementary i j hij a : GL ι F) :
      Matrix ι ι F) =
      1 + single i j a + single j i b + single j j (b * a) := by
    simp only [coe_elementary, Units.val_mul]
    calc (1 + single j i b) * (1 + single i j a)
        = 1 + single i j a + single j i b + single j i b * single i j a := by
          rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one]
          abel
      _ = 1 + single i j a + single j i b + single j j (b * a) := by
          rw [single_mul_single_same]
  have hR : ((elementary i j hij (a / u) *
      (torusGLUnit i j hij v)⁻¹ * elementary j i hij.symm (b / u) : GL ι F) :
        Matrix ι ι F) = diagonal d + single i j a + single j i b +
        single i i (a * (b / u)) := by
    calc _ = (1 + single i j (a / u)) * diagonal d *
          (1 + single j i (b / u)) := by
          simp only [coe_elementary, hDv, Units.val_mul]
      _ = (diagonal d + single i j (a / u) * diagonal d) *
          (1 + single j i (b / u)) := by
          rw [add_mul, one_mul]
      _ = (diagonal d + single i j a) * (1 + single j i (b / u)) := by
          rw [s_mul_d, hd_j, div_mul_cancel₀ a hu0]
      _ = diagonal d + diagonal d * single j i (b / u) +
          single i j a + single i j a * single j i (b / u) := by
          rw [add_mul, mul_add, mul_add, mul_one, mul_one]
          abel
      _ = diagonal d + single j i b + single i j a +
          single i i (a * (b / u)) := by
          have hd : diagonal d * single j i (b / u) = single j i b := by
            rw [d_mul_s, hd_j,
              show u * (b / u) = b from by
                rw [mul_comm, div_mul_cancel₀ b hu0]]
          rw [hd, single_mul_single_same]
      _ = _ := by abel
  have hba : b * a = a * b := mul_comm b a
  have hC1 : u⁻¹ - 1 + a * (b / u) = 0 := by
    calc u⁻¹ - 1 + a * (b / u)
        = u⁻¹ - 1 + a * (b * u⁻¹) := by
          rw [div_eq_mul_inv]
      _ = u⁻¹ - 1 + (a * b) * u⁻¹ := by ring
      _ = u⁻¹ - 1 + (u - 1) * u⁻¹ := by
          have h_ab : a * b = u - 1 := by
            calc a * b = (1 + a * b) - 1 := by ring
              _ = u - 1 := rfl
          rw [h_ab]
      _ = u⁻¹ - 1 + (u * u⁻¹ - 1 * u⁻¹) := by rw [sub_mul]
      _ = u⁻¹ - 1 + (1 - u⁻¹) := by
          rw [mul_inv_cancel₀ hu0, one_mul]
      _ = 0 := by ring
  have hC2 : u - 1 = b * a := by
    calc u - 1 = (1 + a * b) - 1 := rfl
      _ = a * b := by ring
      _ = b * a := by rw [hba]
  apply Units.ext
  rw [hL, hR, hD]
  calc 1 + single i j a + single j i b + single j j (b * a)
      = 1 + single i i (u⁻¹ - 1 + a * (b / u)) + single j j (u - 1) +
        single i j a + single j i b + single i i 0 := by
        simp only [hC1, hC2, single_zero, add_zero]
        abel
    _ = 1 + single i i (u⁻¹ - 1) + single j j (u - 1) +
        single i j a + single j i b + single i i (a * (b / u)) := by
        rw [single_add]
        simp only [single_zero, add_zero]
        abel
    _ = _ := rfl
end Matrix.GeneralLinearGroup
