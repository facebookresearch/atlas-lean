/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.LocalColeHopf
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set ColeHopf

-- The positive-time API must not ask for regularity at zero.
example (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (Ioi 0 ×ˢ (univ : Set ℝ)))
    (t x : ℝ) (ht : 0 < t) (hp : φ t x ≠ 0)
    (hh : ∀ y, deriv (fun s => φ s y) t = ν * iteratedDeriv 2 (φ t) y) :
    deriv (fun s => classicalTransform ν φ s x) t +
      classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x =
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x := by
  exact OnInterval.classicalTransform_burgers isOpen_Ioi isOpen_univ ν φ hφ t x ht
    (mem_univ x) hp (Filter.Eventually.of_forall hh)

-- Nonzero mixed derivatives and a singular time dependence.
private noncomputable def profile (t x : ℝ) : ℝ := Real.exp (x * t⁻¹)
private noncomputable def potential (ν t x : ℝ) : ℝ := -(x + ν) * (t⁻¹) ^ 2

private theorem smooth :
    ContDiffOn ℝ 3 (Function.uncurry profile) (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  (contDiffOn_snd.mul (contDiffOn_fst.inv
    (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) => ne_of_gt hp.1))).exp

private theorem profile_dx (t : ℝ) : deriv (profile t) = fun x => t⁻¹ * profile t x := by
  funext x
  have hd : HasDerivAt (fun y : ℝ => Real.exp (y * t⁻¹))
      (Real.exp (x * t⁻¹) * t⁻¹) x := by
    simpa using! ((hasDerivAt_id' x).mul_const t⁻¹).exp
  change deriv (fun y : ℝ => Real.exp (y * t⁻¹)) x = _
  rw [hd.deriv]
  exact mul_comm _ _

private theorem profile_xx (t x : ℝ) :
    iteratedDeriv 2 (profile t) x = (t⁻¹) ^ 2 * profile t x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, profile_dx, deriv_const_mul_field, profile_dx]
  ring

private theorem profile_heat (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => profile s x) t =
      ν * iteratedDeriv 2 (profile t) x + potential ν t x * profile t x := by
  have hd := (((hasDerivAt_inv (ne_of_gt ht)).const_mul x).exp).deriv
  change deriv (fun s : ℝ => Real.exp (x * s⁻¹)) t = _
  rw [hd, profile_xx]
  simp only [potential, profile]
  ring

-- The spatial potential produces the expected forcing sign and coefficient.
example (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => classicalTransform ν profile s x) t +
        classicalTransform ν profile t x * deriv (classicalTransform ν profile t) x -
        ν * iteratedDeriv 2 (classicalTransform ν profile t) x = 2 * ν * (t⁻¹) ^ 2 := by
  have hF : HasDerivAt (potential ν t) (-(t⁻¹) ^ 2) x := by
    change HasDerivAt (fun y : ℝ => -(y + ν) * (t⁻¹) ^ 2) (-(t⁻¹) ^ 2) x
    simpa only [Pi.neg_apply, neg_mul, one_mul] using!
      (((hasDerivAt_id' x).add_const ν).neg.mul_const ((t⁻¹) ^ 2))
  rw [OnInterval.classicalTransform_forced_burgers isOpen_Ioi isOpen_univ ν profile
    (potential ν) smooth t x ht (mem_univ _) (ne_of_gt (Real.exp_pos _))
    hF.differentiableAt (Filter.Eventually.of_forall (fun y => profile_heat ν t y ht)), hF.deriv]
  ring

-- Joint C² regularity of the transformed field is available only on positive time.
example (ν : ℝ) : ContDiffOn ℝ 2 (Function.uncurry (classicalTransform ν profile))
    (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  OnInterval.classicalTransform_contDiffOn isOpen_Ioi isOpen_univ ν profile smooth
    (fun _ _ => ne_of_gt (Real.exp_pos _))

-- Signed profiles and negative viscosity remain valid locally.
example (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => classicalTransform (-1) (fun _ _ => (-3 : ℝ)) s x) t +
      classicalTransform (-1) (fun _ _ => (-3 : ℝ)) t x *
        deriv (classicalTransform (-1) (fun _ _ => (-3 : ℝ)) t) x =
      (-1) * iteratedDeriv 2 (classicalTransform (-1) (fun _ _ => (-3 : ℝ)) t) x := by
  apply OnInterval.classicalTransform_burgers isOpen_Ioi isOpen_univ (-1)
    (fun _ _ => (-3 : ℝ)) contDiffOn_const t x ht (mem_univ _) (by norm_num)
  exact Filter.Eventually.of_forall (fun y => by norm_num [iteratedDeriv_const])

-- Zero viscosity is allowed in the forward residual identity.
example (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => classicalTransform 0 profile s x) t +
        classicalTransform 0 profile t x * deriv (classicalTransform 0 profile t) x -
        0 * iteratedDeriv 2 (classicalTransform 0 profile t) x = 0 := by
  simpa only [mul_zero, zero_mul] using
    OnInterval.classicalTransform_residual isOpen_Ioi isOpen_univ 0 profile smooth
      t x ht (mem_univ _) (ne_of_gt (Real.exp_pos _))
