/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingInfraredSpatial

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}



noncomputable def isingTorusTwoPoint (beta : Real)
    (x y : IsingDyadicTorus d k) : Real :=
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
      isingTorusSpinField sigma x * isingTorusSpinField sigma y) /
    isingTorusShiftedPartition (d := d) (k := k) beta 0

private theorem isingTorus_weight_translateConfig
    (a : IsingDyadicTorus d k) (beta : Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
        (isingTorusSpinField (isingTorusTranslateConfig a sigma))) =
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) := by
  rw [isingTorusSpinField_translateConfig,
    isingTorusDirichlet_translateField]

private theorem isingTorus_twoPointNumerator_translate
    (a x y : IsingDyadicTorus d k) (beta : Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma (x + a) *
          isingTorusSpinField sigma (y + a)) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x * isingTorusSpinField sigma y := by
  calc
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma (x + a) *
          isingTorusSpinField sigma (y + a)) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) * isingTorusDirichlet
          (isingTorusSpinField (isingTorusTranslateConfig a sigma))) *
        isingTorusSpinField (isingTorusTranslateConfig a sigma) x *
          isingTorusSpinField (isingTorusTranslateConfig a sigma) y := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [isingTorus_weight_translateConfig]
        rfl
    _ = ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x * isingTorusSpinField sigma y := by
      exact (isingTorusTranslateConfigEquiv a).sum_comp (fun sigma =>
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x * isingTorusSpinField sigma y)

theorem isingTorusTwoPoint_translate
    (a x y : IsingDyadicTorus d k) (beta : Real) :
    isingTorusTwoPoint beta (x + a) (y + a) =
      isingTorusTwoPoint beta x y := by
  unfold isingTorusTwoPoint
  rw [isingTorus_twoPointNumerator_translate]

theorem isingTorusTwoPoint_eq_origin_displacement
    (x y : IsingDyadicTorus d k) (beta : Real) :
    isingTorusTwoPoint beta x y = isingTorusTwoPoint beta 0 (y - x) := by
  have h := isingTorusTwoPoint_translate (-x) x y beta
  simpa [sub_eq_add_neg] using h.symm



theorem isingTorusAveragedTwoPoint_eq_twoPoint
    (beta : Real) (z : IsingDyadicTorus d k) :
    isingTorusAveragedTwoPoint beta z = isingTorusTwoPoint beta 0 z := by
  let W : ConfigSpace (IsingDyadicTorus d k) → Real := fun sigma =>
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma))
  let N : IsingDyadicTorus d k → Real := fun x =>
    ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      W sigma * isingTorusSpinField sigma x *
        isingTorusSpinField sigma (x + z)
  have hN (x : IsingDyadicTorus d k) : N x = N 0 := by
    dsimp [N, W]
    have h := isingTorus_twoPointNumerator_translate x 0 z beta
    simpa [add_comm] using h
  have hsum :
      (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          W sigma * ∑ x : IsingDyadicTorus d k,
            isingTorusSpinField sigma x *
              isingTorusSpinField sigma (x + z)) =
        Fintype.card (IsingDyadicTorus d k) * N 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc]
    change (∑ x : IsingDyadicTorus d k, N x) = _
    simp_rw [hN]
    simp
  unfold isingTorusAveragedTwoPoint isingTorusTwoPoint
  change
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        W sigma * ∑ x : IsingDyadicTorus d k,
          isingTorusSpinField sigma x *
            isingTorusSpinField sigma (x + z)) /
      (isingTorusShiftedPartition beta 0 *
        Fintype.card (IsingDyadicTorus d k)) = _
  rw [hsum]
  dsimp [N, W]
  have hZ := (isingTorusShiftedPartition_zero_pos
    (d := d) (k := k) beta).ne'
  have hcard : (Fintype.card (IsingDyadicTorus d k) : Real) ≠ 0 := by
    positivity
  field_simp
  ring

theorem isingTorusTwoPoint_difference_abs_le
    (beta : Real) (hbeta : 0 < beta)
    (x y : IsingDyadicTorus d k) :
    |isingTorusTwoPoint beta 0 x - isingTorusTwoPoint beta 0 y| ≤
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ chi ∈ (Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex)),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            ‖starRingEnd Complex (chi x) - starRingEnd Complex (chi y)‖ := by
  rw [← isingTorusAveragedTwoPoint_eq_twoPoint beta x,
    ← isingTorusAveragedTwoPoint_eq_twoPoint beta y]
  exact isingTorusAveragedTwoPoint_difference_abs_le beta hbeta x y

end StatMech.FrontierA
