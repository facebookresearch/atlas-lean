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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryDiagonal
import Mathlib.Tactic.NoncommRing

/-!
# The rank-one Dennis--Stein matrix identity

Over an arbitrary ring, let `r` and `s` commute and suppose `1 - r * s`
is the value of a unit `u`. The four-factor Dennis--Stein elementary word,
whose coefficients use `u⁻¹`, equals the standard six-factor torus word.
The identity holds at any two distinct coordinates of a finite matrix
index set and does not require the whole ring to be commutative.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [Ring R] {ι : Type*}

private theorem elementary_dennisStein_finTwo
    (r s : R) (hrs : Commute r s) (u : Rˣ) (hu : (u : R) = 1 - r * s) :
    elementary (1 : Fin 2) 0 (by decide) (-(s * (↑u⁻¹ : R))) *
        elementary (0 : Fin 2) 1 (by decide) (-r) *
        elementary (1 : Fin 2) 0 (by decide) s *
        elementary (0 : Fin 2) 1 (by decide) ((↑u⁻¹ : R) * r) =
      (elementary (0 : Fin 2) 1 (by decide) (u : R) *
          elementary (1 : Fin 2) 0 (by decide) (-(↑u⁻¹ : R)) *
          elementary (0 : Fin 2) 1 (by decide) (u : R)) *
        (elementary (0 : Fin 2) 1 (by decide) (-1 : R) *
          elementary (1 : Fin 2) 0 (by decide) (1 : R) *
          elementary (0 : Fin 2) 1 (by decide) (-1 : R)) := by
  have hs_rs : Commute s (r * s) := hrs.symm.mul_right (Commute.refl s)
  have hs_u : Commute s (u : R) := by
    rw [hu]
    exact (Commute.one_right s).sub_right hs_rs
  have hs_uinv : Commute s (↑u⁻¹ : R) := hs_u.units_inv_right
  have hu_mul_inv : (u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  have hinv_mul_u : (↑u⁻¹ : R) * (u : R) = 1 := u.inv_mul
  have hinv_mul_sub : (↑u⁻¹ : R) * (1 - r * s) = 1 := by
    rw [← hu]
    exact hinv_mul_u
  have hinv_sub : (↑u⁻¹ : R) - (↑u⁻¹ : R) * (r * s) = 1 := by
    calc
      (↑u⁻¹ : R) - (↑u⁻¹ : R) * (r * s) =
          (↑u⁻¹ : R) * (1 - r * s) := by noncomm_ring
      _ = 1 := hinv_mul_sub
  have hinv_rs_add_one : (↑u⁻¹ : R) * (r * s) + 1 = (↑u⁻¹ : R) := by
    rw [← hinv_sub]
    abel
  have hs_inv_r_add_one : 1 + s * (↑u⁻¹ : R) * r = (↑u⁻¹ : R) := by
    calc
      1 + s * (↑u⁻¹ : R) * r = 1 + (↑u⁻¹ : R) * (s * r) := by
        rw [hs_uinv.eq, mul_assoc]
      _ = 1 + (↑u⁻¹ : R) * (r * s) := by rw [← hrs.eq]
      _ = (↑u⁻¹ : R) * (r * s) + 1 := add_comm _ _
      _ = (↑u⁻¹ : R) := hinv_rs_add_one
  have h_lower_left :
      -(s * (↑u⁻¹ : R)) + (1 + s * (↑u⁻¹ : R) * r) * s = 0 := by
    rw [hs_inv_r_add_one, ← hs_uinv.eq, neg_add_cancel]
  have h_upper_right : (u : R) * ((↑u⁻¹ : R) * r) + (-r) = 0 := by
    rw [← mul_assoc, hu_mul_inv, one_mul, add_neg_cancel]
  have h_upper : ∀ a : R,
      (↑(elementary (0 : Fin 2) 1 (by decide) a) : Matrix (Fin 2) (Fin 2) R) =
        !![1, a; 0, 1] := by
    intro a
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_elementary]
  have h_lower : ∀ a : R,
      (↑(elementary (1 : Fin 2) 0 (by decide) a) : Matrix (Fin 2) (Fin 2) R) =
        !![1, 0; a, 1] := by
    intro a
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_elementary]
  apply Units.ext
  calc
    (↑(elementary (1 : Fin 2) 0 (by decide) (-(s * (↑u⁻¹ : R))) *
          elementary (0 : Fin 2) 1 (by decide) (-r) *
          elementary (1 : Fin 2) 0 (by decide) s *
          elementary (0 : Fin 2) 1 (by decide) ((↑u⁻¹ : R) * r)) :
        Matrix (Fin 2) (Fin 2) R) =
        !![1, 0; -(s * (↑u⁻¹ : R)), 1] *
          !![1, -r; 0, 1] * !![1, 0; s, 1] *
            !![1, (↑u⁻¹ : R) * r; 0, 1] := by
      simp only [Units.val_mul, h_upper, h_lower]
    _ = !![(u : R), 0; 0, (↑u⁻¹ : R)] := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        simpa [sub_eq_add_neg] using hu.symm
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        simpa [hu, sub_eq_add_neg] using h_upper_right
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        simpa [add_comm] using h_lower_left
      · suffices hscalar :
          (-(s * (↑u⁻¹ : R)) + (s * (↑u⁻¹ : R) * r + 1) * s) *
              ((↑u⁻¹ : R) * r) +
            (s * (↑u⁻¹ : R) * r + 1) = (↑u⁻¹ : R) by
            simpa [Matrix.mul_apply, Fin.sum_univ_two] using hscalar
        have hzero :
            -(s * (↑u⁻¹ : R)) + (s * (↑u⁻¹ : R) * r + 1) * s = 0 := by
          simpa [add_comm] using h_lower_left
        rw [hzero, zero_mul, zero_add]
        simpa [add_comm] using hs_inv_r_add_one
    _ = !![1, (u : R); 0, 1] * !![1, 0; -(↑u⁻¹ : R), 1] *
          !![1, (u : R); 0, 1] *
        (!![1, (-1 : R); 0, 1] * !![1, 0; (1 : R), 1] *
          !![1, (-1 : R); 0, 1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hu_mul_inv, hinv_mul_u]
    _ =
        (↑((elementary (0 : Fin 2) 1 (by decide) (u : R) *
            elementary (1 : Fin 2) 0 (by decide) (-(↑u⁻¹ : R)) *
            elementary (0 : Fin 2) 1 (by decide) (u : R)) *
          (elementary (0 : Fin 2) 1 (by decide) (-1 : R) *
            elementary (1 : Fin 2) 0 (by decide) (1 : R) *
            elementary (0 : Fin 2) 1 (by decide) (-1 : R))) :
          Matrix (Fin 2) (Fin 2) R) := by
      simp only [Units.val_mul, h_upper, h_lower]

/-- Over an arbitrary ring on a finite matrix index set, let `i` and `j`
be distinct. If `r` and `s` commute and the unit `u` has value `1 - r * s`,
then the four-factor Dennis--Stein elementary word, using `u⁻¹`, equals
the six-factor torus word. -/
theorem elementary_dennisStein (i j : ι) [DecidableEq ι] [Fintype ι]
    (hij : i ≠ j) (r s : R) (hrs : Commute r s) (u : Rˣ)
    (hu : (u : R) = 1 - r * s) :
    elementary j i hij.symm (-(s * (↑u⁻¹ : R))) *
        elementary i j hij (-r) * elementary j i hij.symm s *
        elementary i j hij ((↑u⁻¹ : R) * r) =
      (elementary i j hij (u : R) *
          elementary j i hij.symm (-(↑u⁻¹ : R)) *
          elementary i j hij (u : R)) *
        (elementary i j hij (-1 : R) * elementary j i hij.symm (1 : R) *
          elementary i j hij (-1 : R)) := by
  let C := {k : ι // ¬(k = i ∨ k = j)}
  let e : Fin 2 ⊕ C ≃ ι := Matrix.SpecialLinearGroup.pairComplEquiv hij
  let φ : GL (Fin 2) R →* GL ι R :=
    (reindexMulEquiv (A := R) e).toMonoidHom.comp
      (blockDiagonalOne (Fin 2) C R)
  have hi : e (Sum.inl (0 : Fin 2)) = i := by
    have h := Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_i hij
    calc
      e (Sum.inl (0 : Fin 2)) = e (e.symm i) := by rw [h]
      _ = i := e.apply_symm_apply i
  have hj : e (Sum.inl (1 : Fin 2)) = j := by
    have h := Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_j hij
    calc
      e (Sum.inl (1 : Fin 2)) = e (e.symm j) := by rw [h]
      _ = j := e.apply_symm_apply j
  have h01 : ∀ a : R, φ (elementary (0 : Fin 2) 1 (by decide) a) =
      elementary i j hij a := by
    intro a
    calc
      φ (elementary (0 : Fin 2) 1 (by decide) a) =
          reindexMulEquiv e
            (blockDiagonalOne (Fin 2) C R
              (elementary (0 : Fin 2) 1 (by decide) a)) := rfl
      _ = reindexMulEquiv e
          (elementary (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) _ a) := by
            rw [blockDiagonalOne_elementary]
      _ = elementary (e (Sum.inl (0 : Fin 2))) (e (Sum.inl (1 : Fin 2))) _ a := by
            rw [reindexMulEquiv_elementary]
      _ = elementary i j hij a := by
            apply Units.ext
            simp only [coe_elementary]
            rw [hi, hj]
  have h10 : ∀ a : R, φ (elementary (1 : Fin 2) 0 (by decide) a) =
      elementary j i hij.symm a := by
    intro a
    calc
      φ (elementary (1 : Fin 2) 0 (by decide) a) =
          reindexMulEquiv e
            (blockDiagonalOne (Fin 2) C R
              (elementary (1 : Fin 2) 0 (by decide) a)) := rfl
      _ = reindexMulEquiv e
          (elementary (Sum.inl (1 : Fin 2)) (Sum.inl (0 : Fin 2)) _ a) := by
            rw [blockDiagonalOne_elementary]
      _ = elementary (e (Sum.inl (1 : Fin 2))) (e (Sum.inl (0 : Fin 2))) _ a := by
            rw [reindexMulEquiv_elementary]
      _ = elementary j i hij.symm a := by
            apply Units.ext
            simp only [coe_elementary]
            rw [hj, hi]
  have h := congrArg φ (elementary_dennisStein_finTwo r s hrs u hu)
  simpa only [map_mul, h01, h10] using h

end Matrix.GeneralLinearGroup

end
