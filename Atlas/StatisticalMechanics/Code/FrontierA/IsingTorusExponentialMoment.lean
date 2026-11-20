/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusDissemination
import Code.FrontierA.IsingGaussianExponentialTightness





open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}



theorem isingTorus_bilinear_expMoment_le
    (beta : Real)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (t : Real) (h : IsingDyadicTorus d k -> Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (-beta * t *
          isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 <=
        Real.exp ((beta / 2) * t ^ 2 * isingTorusDirichlet h) := by
  let A : Real := ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma)) *
    Real.exp (-beta * t *
      isingTorusDirichletBilinear (isingTorusSpinField sigma) h)
  let Z : Real := isingTorusShiftedPartition (d := d) (k := k) beta 0
  let c : Real := (beta / 2) * t ^ 2 * isingTorusDirichlet h
  have hshift := hdom (t • h)
  rw [isingTorusShiftedPartition_smul] at hshift
  have hshift' : Real.exp (-c) * A <= Z := by
    dsimp only [A, Z, c]
    convert hshift using 1 <;> ring
  have hpos : 0 < Real.exp c := Real.exp_pos c
  have hcancel : Real.exp c * (Real.exp (-c) * A) = A := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hAZ : A <= Real.exp c * Z := by
    have := mul_le_mul_of_nonneg_left hshift' hpos.le
    rwa [hcancel] at this
  have hZ : 0 < Z := isingTorusShiftedPartition_zero_pos beta
  apply (div_le_iff₀ hZ).2
  simpa only [A, Z, c, mul_comm] using hAZ



theorem isingTorus_bilinear_expMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (t : Real) (h : IsingDyadicTorus d k -> Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (-beta * t *
          isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 <=
        Real.exp ((beta / 2) * t ^ 2 * isingTorusDirichlet h) :=
  isingTorus_bilinear_expMoment_le beta
    (isingTorus_gaussianDominated beta hbeta.le) t h

private theorem exp_mul_abs_le_add_exp
    {s x : Real} :
    Real.exp (s * |x|) <= Real.exp (s * x) + Real.exp (-s * x) := by
  by_cases hx : 0 <= x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have heq : s * -x = -s * x := by ring
    rw [heq]
    exact le_add_of_nonneg_left (Real.exp_pos _).le



theorem isingTorus_bilinear_expAbsMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (s : Real)
    (h : IsingDyadicTorus d k -> Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * |beta *
          isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h|)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 <=
        2 * Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h) := by
  let W : ConfigSpace (IsingDyadicTorus d k) -> Real := fun sigma =>
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma))
  let B : ConfigSpace (IsingDyadicTorus d k) -> Real := fun sigma =>
    isingTorusDirichletBilinear (isingTorusSpinField sigma) h
  let Z : Real := isingTorusShiftedPartition (d := d) (k := k) beta 0
  let R : Real := Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h)
  have hpoint (sigma : ConfigSpace (IsingDyadicTorus d k)) :
      W sigma * Real.exp (s * |beta * B sigma|) <=
        W sigma * Real.exp (s * (beta * B sigma)) +
          W sigma * Real.exp (-s * (beta * B sigma)) := by
    calc
      _ <= W sigma * (Real.exp (s * (beta * B sigma)) +
          Real.exp (-s * (beta * B sigma))) :=
        mul_le_mul_of_nonneg_left exp_mul_abs_le_add_exp
          (Real.exp_pos _).le
      _ = _ := by ring
  have hsum :
      (∑ sigma, W sigma * Real.exp (s * |beta * B sigma|)) <=
        (∑ sigma, W sigma * Real.exp (s * (beta * B sigma))) +
          ∑ sigma, W sigma * Real.exp (-s * (beta * B sigma)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun sigma _ => hpoint sigma
  have hplus :
      (∑ sigma, W sigma * Real.exp (s * (beta * B sigma))) / Z <= R := by
    have hmgf := isingTorus_bilinear_expMoment_le_unconditional
      (d := d) (k := k) beta hbeta (-s) h
    dsimp only [W, B, Z, R]
    convert hmgf using 1 <;> ring
  have hminus :
      (∑ sigma, W sigma * Real.exp (-s * (beta * B sigma))) / Z <= R := by
    have hmgf := isingTorus_bilinear_expMoment_le_unconditional
      (d := d) (k := k) beta hbeta s h
    dsimp only [W, B, Z, R]
    convert hmgf using 1 <;> ring
  have hZ : 0 < Z := isingTorusShiftedPartition_zero_pos beta
  apply (div_le_iff₀ hZ).2
  have hplus' := (div_le_iff₀ hZ).1 hplus
  have hminus' := (div_le_iff₀ hZ).1 hminus
  dsimp only [W, B, Z, R] at hsum hplus' hminus' ⊢
  calc
    _ <= (∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * (beta *
          isingTorusDirichletBilinear (isingTorusSpinField sigma) h))) +
      ∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (-s * (beta *
          isingTorusDirichletBilinear (isingTorusSpinField sigma) h)) := hsum
    _ <= Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h) *
          isingTorusShiftedPartition (d := d) (k := k) beta 0 +
        Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h) *
          isingTorusShiftedPartition (d := d) (k := k) beta 0 :=
      add_le_add hplus' hminus'
    _ = 2 * Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h) *
        isingTorusShiftedPartition (d := d) (k := k) beta 0 := by ring

end StatMech.FrontierA
