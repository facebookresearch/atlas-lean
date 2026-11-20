/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusGraphTransition
import Code.FrontierA.TriangularIsingTorusHomology
import Code.Onsager.DecorationSpinGauge










namespace StatMech.FrontierA

open StatMech.Onsager



def triangularTorusXMovementDirection : Fin 6 -> Fin 4 :=
  ![2, 0, 1, 1, 2, 0]



def triangularTorusYMovementDirection : Fin 6 -> Fin 4 :=
  ![0, 0, 3, 1, 3, 1]

def triangularTorusXMovementDart (L : Nat) :
    triangularTorusDart L -> ons_Dart L :=
  fun d => (d.1, triangularTorusXMovementDirection d.2)

def triangularTorusYMovementDart (L : Nat) :
    triangularTorusDart L -> ons_Dart L :=
  fun d => (d.1, triangularTorusYMovementDirection d.2)

@[simp] theorem triangularTorusXMovement_target
    (L : Nat) (d : triangularTorusDart L) :
    (ons_dirStep L (triangularTorusXMovementDirection d.2) d.1).1 =
      (d.1 - triangularTorusDirectionStep L d.2).1 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusXMovementDirection,
      triangularTorusDirectionStep, ons_dirStep] <;> ring

@[simp] theorem triangularTorusYMovement_target
    (L : Nat) (d : triangularTorusDart L) :
    (ons_dirStep L (triangularTorusYMovementDirection d.2) d.1).2 =
      (d.1 - triangularTorusDirectionStep L d.2).2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusYMovementDirection,
      triangularTorusDirectionStep, ons_dirStep] <;> ring



theorem triangularTorusDirectionPhase_eq_movement_zpow
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) :
    triangularTorusDirectionPhase (ons_spinPhase L a)
        (ons_spinPhase L b) d.2 =
      ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusDirectionPhase,
      triangularTorusXMovementDirection,
      triangularTorusYMovementDirection,
      ons_dirExponentX, ons_dirExponentY] <;> ring



noncomputable def triangularTorusSpinVertexGauge
    (L : Nat) (a b : Fin 2) (p : ZMod L × ZMod L) : Complex :=
  ons_spinPhase L a ^ (-(p.1.val : Int)) *
    ons_spinPhase L b ^ (-(p.2.val : Int))

theorem triangularTorusSpinVertexGauge_ne_zero
    (L : Nat) (a b : Fin 2) (p : ZMod L × ZMod L) :
    triangularTorusSpinVertexGauge L a b p ≠ 0 := by
  exact mul_ne_zero
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L a))
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L b))


noncomputable def triangularTorusSpinDartSeamSign
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) : Complex :=
  (-1 : Complex) ^
    (-((a.val : Int) *
        ons_xWrapSign (triangularTorusXMovementDart L d)) -
      (b.val : Int) *
        ons_yWrapSign (triangularTorusYMovementDart L d))

private theorem spinPhase_neg_x_gauge
    (L : Nat) [Fact (2 < L)] (a : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L a ^ (-ons_dirExponentX d.2) *
        ons_spinPhase L a ^ (-(d.1.1.val : Int)) =
      (-1 : Complex) ^ ((a.val : Int) * (-ons_xWrapSign d)) *
        ons_spinPhase L a ^
          (-((ons_dirStep L d.2 d.1).1.val : Int)) := by
  let u := ons_spinPhase L a
  have hu : u ≠ 0 := ons_spinPhase_ne_zero L a
  have hroot : u ^ (L : Int) = (-1 : Complex) ^ (a.val : Int) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hexp := ons_dirExponentX_eq_val_diff_add_wrap d
  have hadd : -ons_dirExponentX d.2 - (d.1.1.val : Int) =
      (-((ons_dirStep L d.2 d.1).1.val : Int)) +
        (L : Int) * (-ons_xWrapSign d) := by
    rw [hexp]
    ring
  change u ^ (-ons_dirExponentX d.2) *
      u ^ (-(d.1.1.val : Int)) = _
  calc
    u ^ (-ons_dirExponentX d.2) * u ^ (-(d.1.1.val : Int)) =
        u ^ (-ons_dirExponentX d.2 - (d.1.1.val : Int)) :=
      (zpow_add₀ hu _ _).symm
    _ = u ^ ((-((ons_dirStep L d.2 d.1).1.val : Int)) +
        (L : Int) * (-ons_xWrapSign d)) := by rw [hadd]
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        u ^ ((L : Int) * (-ons_xWrapSign d)) := zpow_add₀ hu _ _
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        (u ^ (L : Int)) ^ (-ons_xWrapSign d) := by
      rw [_root_.zpow_mul]
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        ((-1 : Complex) ^ (a.val : Int)) ^ (-ons_xWrapSign d) := by
      rw [hroot]
    _ = (-1 : Complex) ^ ((a.val : Int) * (-ons_xWrapSign d)) *
        u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) := by
      rw [← _root_.zpow_mul]
      ring

private theorem spinPhase_neg_y_gauge
    (L : Nat) [Fact (2 < L)] (b : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L b ^ (-ons_dirExponentY d.2) *
        ons_spinPhase L b ^ (-(d.1.2.val : Int)) =
      (-1 : Complex) ^ ((b.val : Int) * (-ons_yWrapSign d)) *
        ons_spinPhase L b ^
          (-((ons_dirStep L d.2 d.1).2.val : Int)) := by
  let v := ons_spinPhase L b
  have hv : v ≠ 0 := ons_spinPhase_ne_zero L b
  have hroot : v ^ (L : Int) = (-1 : Complex) ^ (b.val : Int) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  have hexp := ons_dirExponentY_eq_val_diff_add_wrap d
  have hadd : -ons_dirExponentY d.2 - (d.1.2.val : Int) =
      (-((ons_dirStep L d.2 d.1).2.val : Int)) +
        (L : Int) * (-ons_yWrapSign d) := by
    rw [hexp]
    ring
  change v ^ (-ons_dirExponentY d.2) *
      v ^ (-(d.1.2.val : Int)) = _
  calc
    v ^ (-ons_dirExponentY d.2) * v ^ (-(d.1.2.val : Int)) =
        v ^ (-ons_dirExponentY d.2 - (d.1.2.val : Int)) :=
      (zpow_add₀ hv _ _).symm
    _ = v ^ ((-((ons_dirStep L d.2 d.1).2.val : Int)) +
        (L : Int) * (-ons_yWrapSign d)) := by rw [hadd]
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        v ^ ((L : Int) * (-ons_yWrapSign d)) := zpow_add₀ hv _ _
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        (v ^ (L : Int)) ^ (-ons_yWrapSign d) := by
      rw [_root_.zpow_mul]
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        ((-1 : Complex) ^ (b.val : Int)) ^ (-ons_yWrapSign d) := by
      rw [hroot]
    _ = (-1 : Complex) ^ ((b.val : Int) * (-ons_yWrapSign d)) *
        v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) := by
      rw [← _root_.zpow_mul]
      ring



theorem triangularTorusDirectionPhase_mul_vertexGauge
    (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (d : triangularTorusDart L) :
    triangularTorusDirectionPhase (ons_spinPhase L a)
        (ons_spinPhase L b) d.2 *
        triangularTorusSpinVertexGauge L a b d.1 =
      triangularTorusSpinDartSeamSign L a b d *
        triangularTorusSpinVertexGauge L a b
          (d.1 - triangularTorusDirectionStep L d.2) := by
  rw [triangularTorusDirectionPhase_eq_movement_zpow]
  unfold triangularTorusSpinVertexGauge
    triangularTorusSpinDartSeamSign
  rw [show -((a.val : Int) *
      ons_xWrapSign (triangularTorusXMovementDart L d)) -
      (b.val : Int) *
        ons_yWrapSign (triangularTorusYMovementDart L d) =
      (a.val : Int) *
          (-ons_xWrapSign (triangularTorusXMovementDart L d)) +
        (b.val : Int) *
          (-ons_yWrapSign (triangularTorusYMovementDart L d)) by ring,
    zpow_add₀ (by norm_num : (-1 : Complex) ≠ 0)]
  have hx := spinPhase_neg_x_gauge L a
    (triangularTorusXMovementDart L d)
  have hy := spinPhase_neg_y_gauge L b
    (triangularTorusYMovementDart L d)
  simp only [triangularTorusXMovementDart,
    triangularTorusYMovementDart] at hx hy
  rw [triangularTorusXMovement_target] at hx
  rw [triangularTorusYMovement_target] at hy
  calc
    ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) *
        (ons_spinPhase L a ^ (-(d.1.1.val : Int)) *
          ons_spinPhase L b ^ (-(d.1.2.val : Int))) =
      (ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L a ^ (-(d.1.1.val : Int))) *
      (ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) *
        ons_spinPhase L b ^ (-(d.1.2.val : Int))) := by ring
    _ = _ := by
      rw [hx, hy]
      simp only [triangularTorusXMovementDart,
        triangularTorusYMovementDart]
      ring



noncomputable def triangularTorusSeamKWMatrix
    (L : Nat) (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    Matrix (triangularTorusDart L) (triangularTorusDart L) Complex :=
  fun d e =>
    if (d.1.1 - e.1.1, d.1.2 - e.1.2) =
        triangularTorusDirectionStep L d.2 then
      triangularTorusDirectionWeight t1 t2 t3 d.2 *
        (triangularTorusSpinDartSeamSign L a b d *
          triangularKacWardTurnMatrix rho d.2 e.2)
    else 0


noncomputable def triangularTorusSpinDartGauge
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) : Complex :=
  (triangularTorusSpinVertexGauge L a b d.1)⁻¹

theorem triangularTorusSpinDartGauge_ne_zero
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) :
    triangularTorusSpinDartGauge L a b d ≠ 0 :=
  inv_ne_zero (triangularTorusSpinVertexGauge_ne_zero L a b d.1)



theorem triangularTorusKWMatrix_spin_eq_diagonalGauge_seam
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_diagonalGaugeMatrix (triangularTorusSpinDartGauge L a b)
        (triangularTorusSeamKWMatrix L t1 t2 t3 rho a b) := by
  ext d e
  unfold triangularTorusKWMatrix ons_blockCirculant2D
    triangularTorusKWBlock triangularTorusSeamKWMatrix
    ons_diagonalGaugeMatrix triangularTorusSpinDartGauge
  by_cases hstep : (d.1.1 - e.1.1, d.1.2 - e.1.2) =
      triangularTorusDirectionStep L d.2
  · rw [if_pos hstep]
    simp only [triangularTorusSeamKWMatrix, if_pos hstep]
    have hepos : e.1 = d.1 - triangularTorusDirectionStep L d.2 := by
      rw [← hstep]
      apply Prod.ext <;> simp
    have hg := triangularTorusDirectionPhase_mul_vertexGauge L a b d
    rw [← hepos] at hg
    have hdg := triangularTorusSpinVertexGauge_ne_zero L a b d.1
    have heg := triangularTorusSpinVertexGauge_ne_zero L a b e.1
    field_simp [hdg, heg]
    linear_combination hg *
      (triangularTorusDirectionWeight t1 t2 t3 d.2 *
        triangularKacWardTurnMatrix rho d.2 e.2)
  · rw [if_neg hstep]
    simp only [triangularTorusSeamKWMatrix, if_neg hstep]
    ring


theorem det_ons_diagonalGaugeMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    (gauge : E -> Complex) (hgauge : forall e, gauge e ≠ 0)
    (M : Matrix E E Complex) :
    (ons_diagonalGaugeMatrix gauge M).det = M.det := by
  classical
  let N : Matrix E E Complex := fun i j => gauge i * M i j
  have hleft : Matrix.diagonal gauge * M = N := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, N]
  have hright : N * Matrix.diagonal (fun e => (gauge e)⁻¹) =
        ons_diagonalGaugeMatrix gauge M := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, N,
      ons_diagonalGaugeMatrix]
  have hmatrix : ons_diagonalGaugeMatrix gauge M =
      Matrix.diagonal gauge * M *
        Matrix.diagonal (fun e => (gauge e)⁻¹) := by
    rw [hleft, hright]
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  have hprod : (∏ e, gauge e) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun e _ => hgauge e)
  field_simp [hprod]



theorem det_one_sub_triangularTorusKWMatrix_spin_eq_seam
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho
        (ons_spinPhase L a) (ons_spinPhase L b)).det =
      (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det := by
  rw [triangularTorusKWMatrix_spin_eq_diagonalGauge_seam]
  let gauge := triangularTorusSpinDartGauge L a b
  let M := triangularTorusSeamKWMatrix L t1 t2 t3 rho a b
  have hsub : 1 - ons_diagonalGaugeMatrix gauge M =
      ons_diagonalGaugeMatrix gauge (1 - M) := by
    ext d e
    by_cases hde : d = e
    · subst e
      have hg : gauge d ≠ 0 :=
        triangularTorusSpinDartGauge_ne_zero L a b d
      simp only [Matrix.sub_apply, Matrix.one_apply, if_pos,
        ons_diagonalGaugeMatrix]
      field_simp [hg]
    · simp [ons_diagonalGaugeMatrix, Matrix.one_apply, hde]
  rw [hsub, det_ons_diagonalGaugeMatrix gauge
    (triangularTorusSpinDartGauge_ne_zero L a b)]

end StatMech.FrontierA
