/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingReflectionKernel
import Code.Ising.Gibbs
import Mathlib.Analysis.Calculus.Taylor

open Finset Filter Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising



abbrev IsingDyadicTorus (d k : Nat) := Fin d → ZMod (2 ^ (k + 2))

variable {d k : Nat}


def isingTorusStep (i : Fin d) : IsingDyadicTorus d k :=
  Pi.single i 1



noncomputable def isingTorusDirichletBilinear
    (u v : IsingDyadicTorus d k → Real) : Real :=
  ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
    (u x - u (x + isingTorusStep i)) *
      (v x - v (x + isingTorusStep i))


noncomputable def isingTorusDirichlet
    (u : IsingDyadicTorus d k → Real) : Real :=
  isingTorusDirichletBilinear u u


def isingTorusSpinField
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    IsingDyadicTorus d k → Real :=
  fun x => spin sigma x


noncomputable def isingTorusShiftedPartition
    (beta : Real) (h : IsingDyadicTorus d k → Real) : Real :=
  ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma + h))

theorem isingTorusDirichletBilinear_symm
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear u v =
      isingTorusDirichletBilinear v u := by
  unfold isingTorusDirichletBilinear
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichletBilinear_add_left
    (u v w : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear (u + v) w =
      isingTorusDirichletBilinear u w +
        isingTorusDirichletBilinear v w := by
  unfold isingTorusDirichletBilinear
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichletBilinear_smul_left
    (t : Real) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear (t • u) v =
      t * isingTorusDirichletBilinear u v := by
  unfold isingTorusDirichletBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichlet_add
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (u + v) =
      isingTorusDirichlet u +
        2 * isingTorusDirichletBilinear u v +
        isingTorusDirichlet v := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  simp only [Pi.add_apply]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isingTorusDirichlet_smul
    (t : Real) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (t • u) =
      t ^ 2 * isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring



theorem isingTorusShiftedPartition_smul
    (beta t : Real) (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta (t • h) =
      Real.exp (-(beta / 2) * t ^ 2 * isingTorusDirichlet h) *
        ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          Real.exp (-beta * t *
            isingTorusDirichletBilinear
              (isingTorusSpinField sigma) h) := by
  unfold isingTorusShiftedPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [isingTorusDirichlet_add,
    isingTorusDirichlet_smul,
    isingTorusDirichletBilinear_symm
      (isingTorusSpinField sigma) (t • h),
    isingTorusDirichletBilinear_smul_left,
    isingTorusDirichletBilinear_symm h (isingTorusSpinField sigma),
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem isingTorusShiftedPartition_zero_pos (beta : Real) :
    0 < isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
  unfold isingTorusShiftedPartition
  exact Finset.sum_pos (fun sigma _ => Real.exp_pos _) Finset.univ_nonempty


def IsingTorusGaussianDominated (beta : Real) : Prop :=
  ∀ h : IsingDyadicTorus d k → Real,
    isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0





theorem iteratedDeriv_two_nonpos_of_global_max
    (f : Real → Real) (hf : ContDiff Real 2 f)
    (hmax : ∀ x, f x ≤ f 0) :
    iteratedDeriv 2 f 0 ≤ 0 := by
  have hm : IsLocalMax f 0 := Filter.Eventually.of_forall hmax
  have hd : deriv f 0 = 0 := hm.deriv_eq_zero
  have hpoly (x : Real) : taylorWithinEval f 2 Set.univ 0 x =
      f 0 + (iteratedDeriv 2 f 0 / 2) * x ^ 2 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0,
      taylor_within_zero_eval]
    simp [iteratedDerivWithin_univ, hd]
    ring
  have ht := Real.taylor_tendsto (f := f) (x₀ := 0) (n := 2)
    convex_univ (mem_univ 0) hf.contDiffOn
  simp only [hpoly, sub_zero] at ht
  have ht' : Tendsto (fun x =>
      (f x - (f 0 + iteratedDeriv 2 f 0 / 2 * x ^ 2)) / x ^ 2)
      (nhds 0) (nhds 0) := by simpa using ht
  have hadd := ht'.add
    (tendsto_const_nhds : Tendsto
      (fun _ : Real => iteratedDeriv 2 f 0 / 2)
      (nhds 0) (nhds (iteratedDeriv 2 f 0 / 2)))
  have hadd' : Tendsto (fun x =>
      (f x - (f 0 + iteratedDeriv 2 f 0 / 2 * x ^ 2)) / x ^ 2 +
        iteratedDeriv 2 f 0 / 2) (nhds 0)
      (nhds (iteratedDeriv 2 f 0 / 2)) := by simpa using hadd
  have hratio : Tendsto (fun x : Real => (f x - f 0) / x ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (iteratedDeriv 2 f 0 / 2)) := by
    apply hadd'.mono_left inf_le_left |>.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp
    ring
  have hle : iteratedDeriv 2 f 0 / 2 ≤ 0 :=
    le_of_tendsto hratio (Filter.Eventually.of_forall (fun x =>
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hmax x)) (sq_nonneg x)))
  linarith

private noncomputable def isingTorusShiftedPartitionLineDeriv
    (beta : Real) (h : IsingDyadicTorus d k → Real) (t : Real) : Real :=
  ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma + t • h)) *
    (-beta * (isingTorusDirichletBilinear
      (isingTorusSpinField sigma) h + t * isingTorusDirichlet h))

private theorem hasDerivAt_isingTorusShiftedWeight_line
    (beta : Real) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) (t : Real) :
    HasDerivAt (fun s : Real =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + s • h)))
      (Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma + t • h)) *
        (-beta * (isingTorusDirichletBilinear
          (isingTorusSpinField sigma) h + t * isingTorusDirichlet h))) t := by
  have hq : HasDerivAt (fun s : Real =>
      -(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + s • h))
      (-beta * (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) h + t * isingTorusDirichlet h)) t := by
    rw [show (fun s : Real => -(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + s • h)) =
      fun s => -(beta / 2) *
        (isingTorusDirichlet (isingTorusSpinField sigma) +
          2 * s * isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h +
          s ^ 2 * isingTorusDirichlet h) by
        funext s
        rw [isingTorusDirichlet_add, isingTorusDirichlet_smul,
          isingTorusDirichletBilinear_symm
            (isingTorusSpinField sigma) (s • h),
          isingTorusDirichletBilinear_smul_left,
          isingTorusDirichletBilinear_symm h
            (isingTorusSpinField sigma)]
        ring]
    convert (((hasDerivAt_id t).const_mul 2 |>.mul_const
      (isingTorusDirichletBilinear (isingTorusSpinField sigma) h)).add
        (((hasDerivAt_id t).pow 2).mul_const
          (isingTorusDirichlet h))).const_add
            (isingTorusDirichlet (isingTorusSpinField sigma))
          |>.const_mul (-(beta / 2)) using 1
    · funext s
      simp only [id_eq, Pi.add_apply, Pi.pow_apply]
      ring
    · simp only [id_eq]
      ring
  exact hq.exp

theorem hasDerivAt_isingTorusShiftedPartition_line
    (beta : Real) (h : IsingDyadicTorus d k → Real) (t : Real) :
    HasDerivAt (fun s => isingTorusShiftedPartition beta (s • h))
      (isingTorusShiftedPartitionLineDeriv beta h t) t := by
  unfold isingTorusShiftedPartition isingTorusShiftedPartitionLineDeriv
  apply HasDerivAt.fun_sum
  intro sigma _
  exact hasDerivAt_isingTorusShiftedWeight_line beta h sigma t

theorem hasDerivAt_isingTorusShiftedPartitionLineDeriv_zero
    (beta : Real) (h : IsingDyadicTorus d k → Real) :
    HasDerivAt (isingTorusShiftedPartitionLineDeriv beta h)
      (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        ((beta * isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h) ^ 2 -
          beta * isingTorusDirichlet h)) 0 := by
  unfold isingTorusShiftedPartitionLineDeriv
  apply HasDerivAt.fun_sum
  intro sigma _
  have hterm : HasDerivAt (fun t : Real =>
      -beta * (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) h + t * isingTorusDirichlet h))
      (-beta * isingTorusDirichlet h) 0 := by
    convert ((hasDerivAt_id 0).mul_const
      (isingTorusDirichlet h)).const_add
        (isingTorusDirichletBilinear (isingTorusSpinField sigma) h)
      |>.const_mul (-beta) using 1 <;> ring
  have hq : HasDerivAt (fun t : Real =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + t • h)))
      (Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        (-beta * isingTorusDirichletBilinear
          (isingTorusSpinField sigma) h)) 0 := by
    simpa only [zero_smul, add_zero, zero_mul, add_zero] using
      hasDerivAt_isingTorusShiftedWeight_line beta h sigma 0
  convert hq.mul hterm using 1 <;>
    simp only [zero_smul, add_zero, zero_mul] <;> ring


theorem iteratedDeriv_two_isingTorusShiftedPartition_line_zero
    (beta : Real) (h : IsingDyadicTorus d k → Real) :
    iteratedDeriv 2
      (fun t : Real => isingTorusShiftedPartition beta (t • h)) 0 =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        ((beta * isingTorusDirichletBilinear
            (isingTorusSpinField sigma) h) ^ 2 -
          beta * isingTorusDirichlet h) := by
  rw [show iteratedDeriv 2
      (fun t : Real => isingTorusShiftedPartition beta (t • h)) =
      deriv (deriv
        (fun t : Real => isingTorusShiftedPartition beta (t • h))) by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero]]
  have hderiv : deriv
      (fun t => isingTorusShiftedPartition beta (t • h)) =
      isingTorusShiftedPartitionLineDeriv beta h := by
    funext t
    exact (hasDerivAt_isingTorusShiftedPartition_line beta h t).deriv
  rw [hderiv]
  exact (hasDerivAt_isingTorusShiftedPartitionLineDeriv_zero beta h).deriv

theorem contDiff_isingTorusShiftedPartition_line
    (beta : Real) (h : IsingDyadicTorus d k → Real) :
    ContDiff Real 2
      (fun t : Real => isingTorusShiftedPartition beta (t • h)) := by
  have heq : (fun t : Real => isingTorusShiftedPartition beta (t • h)) =
      fun t : Real => ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) +
            2 * t * isingTorusDirichletBilinear
              (isingTorusSpinField sigma) h +
            t ^ 2 * isingTorusDirichlet h)) := by
    funext t
    unfold isingTorusShiftedPartition
    apply Finset.sum_congr rfl
    intro sigma _
    rw [isingTorusDirichlet_add, isingTorusDirichlet_smul,
      isingTorusDirichletBilinear_symm
        (isingTorusSpinField sigma) (t • h),
      isingTorusDirichletBilinear_smul_left,
      isingTorusDirichletBilinear_symm h
        (isingTorusSpinField sigma)]
    ring
  rw [heq]
  fun_prop



theorem isingTorus_bilinear_secondMoment_le_dirichlet
    (beta : Real) (hbeta : 0 < beta)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (h : IsingDyadicTorus d k → Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        (isingTorusDirichletBilinear
          (isingTorusSpinField sigma) h) ^ 2) ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0 *
        (isingTorusDirichlet h / beta) := by
  let f : Real → Real := fun t =>
    isingTorusShiftedPartition (d := d) (k := k) beta (t • h)
  have hsecond : iteratedDeriv 2 f 0 ≤ 0 :=
    iteratedDeriv_two_nonpos_of_global_max f
      (contDiff_isingTorusShiftedPartition_line
        (d := d) (k := k) beta h)
      (fun t => by simpa only [f, zero_smul] using hdom (t • h))
  rw [iteratedDeriv_two_isingTorusShiftedPartition_line_zero
    (d := d) (k := k) beta h] at hsecond
  let W : ConfigSpace (IsingDyadicTorus d k) → Real := fun sigma =>
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma))
  let B : ConfigSpace (IsingDyadicTorus d k) → Real := fun sigma =>
    isingTorusDirichletBilinear (isingTorusSpinField sigma) h
  let D : Real := isingTorusDirichlet h
  have hZ : isingTorusShiftedPartition (d := d) (k := k) beta 0 =
      ∑ sigma, W sigma := by
    unfold isingTorusShiftedPartition W
    simp
  have hexpand : (∑ sigma, W sigma * ((beta * B sigma) ^ 2 - beta * D)) =
      beta ^ 2 * (∑ sigma, W sigma * (B sigma) ^ 2) -
        beta * D * (∑ sigma, W sigma) := by
    calc
      (∑ sigma, W sigma * ((beta * B sigma) ^ 2 - beta * D)) =
          ∑ sigma, (beta ^ 2 * (W sigma * B sigma ^ 2) -
            beta * D * W sigma) := by
        apply Finset.sum_congr rfl
        intro sigma _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (∑ sigma, W sigma * ((beta * B sigma) ^ 2 - beta * D)) ≤ 0 at hsecond
  rw [hexpand] at hsecond
  change (∑ sigma, W sigma * (B sigma) ^ 2) ≤ _
  rw [hZ]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hbeta).2
  nlinarith


end StatMech.FrontierA
