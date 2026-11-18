/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

/-!
# Poroelastic port-energy identity

## i. Overview

For a finite poroelastic port network with displacement and
pressure trajectories satisfying `K*u - Q*p = f` and
`C*p' + Q^T*u' + H*p = s` for constant symmetric storage
matrices `K` and `C`, the stored quadratic energy
`(1/2) * (u^T K u + p^T C p)` has derivative equal to the input
power `u'^T f + p^T s` minus the dissipation `p^T H p`. The two
coupling powers cancel because the ports carry opposite signs.

## ii. Key results

- `Mechanics.Poroelastic.poroelastic_port_energy`: the
  port-energy identity.

## iii. Table of contents

- A. Port-energy identity

## iv. References

- M. A. Biot, mechanics of deformation and acoustic
  propagation in porous media, *J. Appl. Phys.* 33, 1962
  (coupled solid-fluid energy balance).
-/

@[expose] public section

open Matrix

namespace Mechanics.Poroelastic

/-! ## A. Port-energy identity -/

theorem hasDerivAt_mulVec_coord {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} {x : ℝ → n → ℝ} {dx : n → ℝ} {t : ℝ}
    (hx : ∀ j, HasDerivAt (fun τ => x τ j) (dx j) t)
    (i : n) : HasDerivAt (fun τ => (M *ᵥ x τ) i) ((M *ᵥ dx) i) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => HasDerivAt.const_mul (M i j) (hx j))
  simpa [Matrix.mulVec, dotProduct] using h

theorem hasDerivAt_dotProduct {n : Type*} [Fintype n]
    {x : ℝ → n → ℝ} {dx : n → ℝ} {y : ℝ → n → ℝ} {dy : n → ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun τ => x τ i) (dx i) t)
    (hy : ∀ i, HasDerivAt (fun τ => y τ i) (dy i) t) :
    HasDerivAt (fun τ => (x τ) ⬝ᵥ (y τ)) ((dx ⬝ᵥ y t) + (x t ⬝ᵥ dy)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hx i).mul (hy i))
  simpa [dotProduct, Finset.sum_add_distrib, Pi.mul_apply] using h

/-- Finite poroelastic port-energy identity. Along differentiable
trajectories `u` (displacement) and `p` (pressure) with supplied
derivative functions satisfying, at every time,
`K*u - Q*p = f` and `C*p' + Qᵀ*u' + H*p = s`, for constant
symmetric storage matrices `K` and `C`, the stored quadratic
energy `1/2 * (uᵀKu + pᵀCp)` has derivative equal to input power
`u'ᵀf + pᵀs` minus dissipation `pᵀHp`. The opposite signs of the
two coupling terms are essential. -/
theorem poroelastic_port_energy {n : Type*} [Fintype n]
    {K Q C H : Matrix n n ℝ} (hK : K.IsSymm) (hC : C.IsSymm)
    {u p du dp f s : ℝ → n → ℝ}
    (hu : ∀ i t, HasDerivAt (fun τ => u τ i) (du t i) t)
    (hp : ∀ i t, HasDerivAt (fun τ => p τ i) (dp t i) t)
    (hmech : ∀ t, K *ᵥ u t - Q *ᵥ p t = f t)
    (hfluid : ∀ t, C *ᵥ dp t + Qᵀ *ᵥ du t + H *ᵥ p t = s t)
    (t : ℝ) :
    HasDerivAt
      (fun τ => (1 / 2)
        * ((u τ) ⬝ᵥ (K *ᵥ u τ) + (p τ) ⬝ᵥ (C *ᵥ p τ)))
      ((du t) ⬝ᵥ (f t) + (p t) ⬝ᵥ (s t)
        - (p t) ⬝ᵥ (H *ᵥ p t)) t := by
  have hKu : ∀ i, HasDerivAt (fun τ => (K *ᵥ u τ) i) ((K *ᵥ du t) i) t :=
    fun i => hasDerivAt_mulVec_coord (fun j => hu j t) i
  have hE1 : HasDerivAt (fun τ => (u τ) ⬝ᵥ (K *ᵥ u τ))
      ((du t ⬝ᵥ (K *ᵥ u t)) + (u t ⬝ᵥ (K *ᵥ du t))) t :=
    hasDerivAt_dotProduct (fun i => hu i t) hKu
  have hCp : ∀ i, HasDerivAt (fun τ => (C *ᵥ p τ) i) ((C *ᵥ dp t) i) t :=
    fun i => hasDerivAt_mulVec_coord (fun j => hp j t) i
  have hE2 : HasDerivAt (fun τ => (p τ) ⬝ᵥ (C *ᵥ p τ))
      ((dp t ⬝ᵥ (C *ᵥ p t)) + (p t ⬝ᵥ (C *ᵥ dp t))) t :=
    hasDerivAt_dotProduct (fun i => hp i t) hCp
  have hSum := hE1.add hE2
  have hEnergy := HasDerivAt.const_mul (1 / 2) hSum
  have hsymK : (u t) ⬝ᵥ (K *ᵥ du t) = (du t) ⬝ᵥ (K *ᵥ u t) :=
    hK.dotProduct_mulVec_comm
  have hsymC : (p t) ⬝ᵥ (C *ᵥ dp t) = (dp t) ⬝ᵥ (C *ᵥ p t) :=
    hC.dotProduct_mulVec_comm
  have hcancel : (du t) ⬝ᵥ (Q *ᵥ p t) = (p t) ⬝ᵥ (Qᵀ *ᵥ du t) :=
    (Matrix.dotProduct_transpose_mulVec Q (p t) (du t)).symm
  have hmech_dp : (du t) ⬝ᵥ (K *ᵥ u t) - (du t) ⬝ᵥ (Q *ᵥ p t)
      = (du t) ⬝ᵥ f t := by
    have hcongr : (du t) ⬝ᵥ (K *ᵥ u t - Q *ᵥ p t) = (du t) ⬝ᵥ f t := by
      rw [hmech t]
    rwa [dotProduct_sub] at hcongr
  have hfluid_dp : (p t) ⬝ᵥ (C *ᵥ dp t) + (p t) ⬝ᵥ (Qᵀ *ᵥ du t)
      + (p t) ⬝ᵥ (H *ᵥ p t) = (p t) ⬝ᵥ s t := by
    have hcongr : (p t) ⬝ᵥ (C *ᵥ dp t + Qᵀ *ᵥ du t + H *ᵥ p t)
        = (p t) ⬝ᵥ s t := by
      rw [hfluid t]
    rwa [dotProduct_add, dotProduct_add] at hcongr
  have hval : (1 / 2 : ℝ) * (((du t ⬝ᵥ (K *ᵥ u t)) + (u t ⬝ᵥ (K *ᵥ du t))) +
      ((dp t ⬝ᵥ (C *ᵥ p t)) + (p t ⬝ᵥ (C *ᵥ dp t)))) =
      (du t ⬝ᵥ f t) + (p t ⬝ᵥ s t) - (p t ⬝ᵥ (H *ᵥ p t)) := by
    rw [hsymK, hsymC]
    linarith [hmech_dp, hfluid_dp, hcancel]
  simp only [Pi.add_apply] at hEnergy
  rw [hval] at hEnergy
  exact hEnergy

end Mechanics.Poroelastic
