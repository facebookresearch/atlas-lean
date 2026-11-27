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
import MathlibExt.Analysis.Calculus.QuadraticDerivative
import Mathlib.Tactic.Linarith

/-!
# Vibroacoustic port-energy identity

## i. Overview

For a coupled structural-acoustic system with structural
displacement `x`, velocity `v = x'`, acoustic pressure `p`, and
constant symmetric matrices `M`, `K`, `A` satisfying
`M*dv + C*v + K*x - G*p = 0` and `A*dp + H*p + G^T*v = 0`, the
quadratic form `(1/2) * (v^T M v + x^T K x + p^T A p)` has
derivative `-(v^T C v + p^T H p)`: the reciprocal coupling
power through `G` and `G^T` cancels. This is the algebraic
quadratic balance; reading the quadratic form as stored
energy and the two remaining terms as dissipation uses the
usual positivity (positive semidefinite storage matrices
`M`, `K`, `A` and damping matrices `C`, `H`), which the
identity itself does not assume. The identity is pointwise in
time; the all-times form is the corollary for trajectories
satisfying the derivative and balance hypotheses at every time.

## ii. Key results

- `Mechanics.Vibroacoustic.vibroacoustic_port_energy`: the
  pointwise port-energy identity.
- `Mechanics.Vibroacoustic.vibroacoustic_port_energy_all_times`:
  the all-times form.

## iii. Table of contents

- A. Port-energy identity

## iv. References

- F. Fahy and P. Gardonio, *Sound and Structural Vibration:
  Radiation, Transmission and Response*, 2nd edition,
  Academic Press, 2007, Chapter 4 (coupled
  structural-acoustic power and energy balance with
  reciprocal coupling between structural velocity and
  acoustic pressure).
-/

@[expose] public section

open Matrix

namespace Mechanics.Vibroacoustic

/-! ## A. Port-energy identity -/

private lemma quad_hasDerivAt {n : Type*} [Fintype n]
    {S : Matrix n n ℝ} (hS : S.IsSymm)
    {u du : ℝ → n → ℝ} (t : ℝ)
    (hu : ∀ i, HasDerivAt (fun τ => u τ i) (du t i) t) :
    HasDerivAt (fun τ => (u τ) ⬝ᵥ (S *ᵥ u τ))
      (2 * ((u t) ⬝ᵥ (S *ᵥ du t))) t := by
  have h := QuadraticDerivative.hasDerivAt_quadForm_half S hS u (du t) t hu
  have h2 := h.const_mul (2 : ℝ)
  have hfun : (fun τ => (u τ) ⬝ᵥ (S *ᵥ u τ))
      = fun τ => 2 *
        (MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm
          S (u τ) / 2) := by
    funext τ
    simp [MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm]
    ring
  have hval : (2 : ℝ) * (∑ i, ∑ j, du t i * S i j * u t j)
      = 2 * ((u t) ⬝ᵥ (S *ᵥ du t)) := by
    have hsum : (∑ i, ∑ j, du t i * S i j * u t j)
        = (du t) ⬝ᵥ (S *ᵥ u t) := by
      rw [Matrix.dot_mulVec_eq_sum_sum]
      exact Finset.sum_comm
    rw [hsum, hS.dotProduct_mulVec_comm]
  simpa only [hfun, hval] using h2

/-- Reciprocal-port vibroacoustic quadratic-balance identity at a
fixed time `t`. For structural displacement `x` differentiable at
`t`, with velocity value `v t` and derivative value `dv t`, and
acoustic pressure `p` with derivative value `dp t`, satisfying at
`t`
`M*dv + C*v + K*x - G*p = 0` and `A*dp + H*p + Gᵀ*v = 0`, with
constant symmetric matrices `M`, `K`, and `A`, the quadratic form
`1/2 * (vᵀMv + xᵀKx + pᵀAp)` has derivative `-(vᵀCv + pᵀHp)` at
`t`: the reciprocal coupling power cancels. The
stored-energy/dissipation reading additionally requires the usual
positivity of the storage and damping matrices, which this
algebraic identity does not assume. -/
theorem vibroacoustic_port_energy {n m : Type*} [Fintype n]
    [Fintype m] {M K C : Matrix n n ℝ} {A H : Matrix m m ℝ}
    {G : Matrix n m ℝ} (hM : M.IsSymm) (hK : K.IsSymm)
    (hA : A.IsSymm)
    {x v dv : ℝ → n → ℝ} {p dp : ℝ → m → ℝ}
    (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun τ => x τ i) (v t i) t)
    (hv : ∀ i, HasDerivAt (fun τ => v τ i) (dv t i) t)
    (hp : ∀ i, HasDerivAt (fun τ => p τ i) (dp t i) t)
    (hstruct : M *ᵥ dv t + C *ᵥ v t + K *ᵥ x t
      - G *ᵥ p t = 0)
    (hacous : A *ᵥ dp t + H *ᵥ p t + Gᵀ *ᵥ v t = 0) :
    HasDerivAt
      (fun τ => (1 / 2)
        * ((v τ) ⬝ᵥ (M *ᵥ v τ) + (x τ) ⬝ᵥ (K *ᵥ x τ)
          + (p τ) ⬝ᵥ (A *ᵥ p τ)))
      (-(((v t) ⬝ᵥ (C *ᵥ v t)) + ((p t) ⬝ᵥ (H *ᵥ p t)))) t := by
  have hM' : HasDerivAt (fun τ => (v τ) ⬝ᵥ (M *ᵥ v τ))
      (2 * ((v t) ⬝ᵥ (M *ᵥ dv t))) t := quad_hasDerivAt hM t hv
  have hK' : HasDerivAt (fun τ => (x τ) ⬝ᵥ (K *ᵥ x τ))
      (2 * ((x t) ⬝ᵥ (K *ᵥ v t))) t := quad_hasDerivAt hK t hx
  have hA' : HasDerivAt (fun τ => (p τ) ⬝ᵥ (A *ᵥ p τ))
      (2 * ((p t) ⬝ᵥ (A *ᵥ dp t))) t := quad_hasDerivAt hA t hp
  have hfull := HasDerivAt.const_mul (1 / 2) ((hM'.add hK').add hA')
  have hKt : Kᵀ = K := hK
  have hKsym : (x t) ⬝ᵥ (K *ᵥ v t) = (v t) ⬝ᵥ (K *ᵥ x t) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hKt, dotProduct_comm]
  have hcoup : (v t) ⬝ᵥ (G *ᵥ p t) = (p t) ⬝ᵥ (Gᵀ *ᵥ v t) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have hvd : (v t) ⬝ᵥ (M *ᵥ dv t + C *ᵥ v t + K *ᵥ x t - G *ᵥ p t) = 0 := by
    rw [hstruct]
    exact dotProduct_zero _
  have h1 : ((v t) ⬝ᵥ (M *ᵥ dv t)) + ((v t) ⬝ᵥ (C *ᵥ v t))
      + ((v t) ⬝ᵥ (K *ᵥ x t)) - ((v t) ⬝ᵥ (G *ᵥ p t)) = 0 := by
    have h := hvd
    rwa [dotProduct_sub, dotProduct_add, dotProduct_add] at h
  have hpd : (p t) ⬝ᵥ (A *ᵥ dp t + H *ᵥ p t + Gᵀ *ᵥ v t) = 0 := by
    rw [hacous]
    exact dotProduct_zero _
  have h2 : ((p t) ⬝ᵥ (A *ᵥ dp t)) + ((p t) ⬝ᵥ (H *ᵥ p t))
      + ((p t) ⬝ᵥ (Gᵀ *ᵥ v t)) = 0 := by
    have h := hpd
    rwa [dotProduct_add, dotProduct_add] at h
  have hDeq : (1 / 2) * ((2 * ((v t) ⬝ᵥ (M *ᵥ dv t))
      + 2 * ((x t) ⬝ᵥ (K *ᵥ v t))) + 2 * ((p t) ⬝ᵥ (A *ᵥ dp t)))
      = -(((v t) ⬝ᵥ (C *ᵥ v t)) + ((p t) ⬝ᵥ (H *ᵥ p t))) := by
    rw [hKsym]
    linarith [h1, h2, hcoup]
  rw [hDeq] at hfull
  exact hfull

/-- All-times form of the reciprocal-port vibroacoustic
quadratic-balance identity: with constant symmetric `M`, `K` and `A`,
if the derivative hypotheses and the balance equations
`M*dv + C*v + K*x - G*p = 0` and `A*dp + H*p + Gᵀ*v = 0` hold at every
time, then `1/2 * (vᵀMv + xᵀKx + pᵀAp)` has derivative `-(vᵀCv + pᵀHp)`
at each time `t`. -/
theorem vibroacoustic_port_energy_all_times {n m : Type*}
    [Fintype n] [Fintype m] {M K C : Matrix n n ℝ}
    {A H : Matrix m m ℝ} {G : Matrix n m ℝ} (hM : M.IsSymm)
    (hK : K.IsSymm) (hA : A.IsSymm)
    {x v dv : ℝ → n → ℝ} {p dp : ℝ → m → ℝ}
    (hx : ∀ i t, HasDerivAt (fun τ => x τ i) (v t i) t)
    (hv : ∀ i t, HasDerivAt (fun τ => v τ i) (dv t i) t)
    (hp : ∀ i t, HasDerivAt (fun τ => p τ i) (dp t i) t)
    (hstruct : ∀ t, M *ᵥ dv t + C *ᵥ v t + K *ᵥ x t
      - G *ᵥ p t = 0)
    (hacous : ∀ t, A *ᵥ dp t + H *ᵥ p t + Gᵀ *ᵥ v t = 0)
    (t : ℝ) :
    HasDerivAt
      (fun τ => (1 / 2)
        * ((v τ) ⬝ᵥ (M *ᵥ v τ) + (x τ) ⬝ᵥ (K *ᵥ x τ)
          + (p τ) ⬝ᵥ (A *ᵥ p τ)))
      (-(((v t) ⬝ᵥ (C *ᵥ v t)) + ((p t) ⬝ᵥ (H *ᵥ p t)))) t := by
  exact vibroacoustic_port_energy hM hK hA t (fun i => hx i t)
    (fun i => hv i t) (fun i => hp i t) (hstruct t) (hacous t)
end Mechanics.Vibroacoustic
