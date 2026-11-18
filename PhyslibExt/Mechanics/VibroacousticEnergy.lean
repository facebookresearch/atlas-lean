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
identity itself does not assume.

## ii. Key results

- `Mechanics.Vibroacoustic.vibroacoustic_port_energy`: the
  port-energy identity.

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
    {S : Matrix n n ℝ}
    {u du : ℝ → n → ℝ}
    (hu : ∀ i t, HasDerivAt (fun τ => u τ i) (du t i) t)
    (t : ℝ) :
    HasDerivAt (fun τ => (u τ) ⬝ᵥ (S *ᵥ u τ))
      ((du t) ⬝ᵥ (S *ᵥ u t) + (u t) ⬝ᵥ (S *ᵥ du t)) t := by
  have hrow : ∀ i : n, HasDerivAt (fun τ => (S *ᵥ u τ) i) ((S *ᵥ du t) i) t := by
    intro i
    have hterm : ∀ j : n, HasDerivAt (fun τ => S i j * u τ j) (S i j * du t j) t :=
      fun j => HasDerivAt.const_mul _ (hu j t)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
    have hfun : (fun τ => (S *ᵥ u τ) i)
        = (fun τ => ∑ j ∈ Finset.univ, S i j * u τ j) := rfl
    have hval : (∑ j ∈ Finset.univ, S i j * du t j) = (S *ᵥ du t) i := rfl
    rw [hfun, ← hval]
    exact hsum
  have hcoord : ∀ i : n, HasDerivAt (fun τ => u τ i * (S *ᵥ u τ) i)
      (du t i * (S *ᵥ u t) i + u t i * (S *ᵥ du t) i) t :=
    fun i => (hu i t).mul (hrow i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcoord i)
  have hfun : (fun τ => (u τ) ⬝ᵥ (S *ᵥ u τ))
      = (fun τ => ∑ i ∈ Finset.univ, u τ i * (S *ᵥ u τ) i) := rfl
  have hval : (∑ i ∈ Finset.univ, (du t i * (S *ᵥ u t) i + u t i * (S *ᵥ du t) i))
      = (du t) ⬝ᵥ (S *ᵥ u t) + (u t) ⬝ᵥ (S *ᵥ du t) :=
    Finset.sum_add_distrib.trans rfl
  rw [hfun, ← hval]
  exact hsum

private lemma symm_dot_swap {n : Type*} [Fintype n]
    {S : Matrix n n ℝ} (hS : S.IsSymm)
    (a b : n → ℝ) : a ⬝ᵥ (S *ᵥ b) = b ⬝ᵥ (S *ᵥ a) := by
  have hSeq : Sᵀ = S := hS
  calc a ⬝ᵥ (S *ᵥ b) = (a ᵥ* S) ⬝ᵥ b := Matrix.dotProduct_mulVec a S b
    _ = (Sᵀ *ᵥ a) ⬝ᵥ b := by rw [← Matrix.mulVec_transpose S a]
    _ = (S *ᵥ a) ⬝ᵥ b := by rw [hSeq]
    _ = b ⬝ᵥ (S *ᵥ a) := dotProduct_comm _ _

private lemma couple_dot_swap {n m : Type*} [Fintype n] [Fintype m]
    {G : Matrix n m ℝ} (v : n → ℝ) (p : m → ℝ) :
    v ⬝ᵥ (G *ᵥ p) = p ⬝ᵥ (Gᵀ *ᵥ v) := by
  calc v ⬝ᵥ (G *ᵥ p) = (v ᵥ* G) ⬝ᵥ p := Matrix.dotProduct_mulVec v G p
    _ = (Gᵀ *ᵥ v) ⬝ᵥ p := by rw [← Matrix.mulVec_transpose G v]
    _ = p ⬝ᵥ (Gᵀ *ᵥ v) := dotProduct_comm _ _

/-- Reciprocal-port vibroacoustic quadratic-balance identity.
Along differentiable structural displacement `x` with velocity
`v` and acoustic pressure `p` with derivative function `dp`,
satisfying at every time `M*dv + C*v + K*x - G*p = 0` and
`A*dp + H*p + Gᵀ*v = 0`, with constant symmetric matrices
`M`, `K`, and `A`, the quadratic form
`1/2 * (vᵀMv + xᵀKx + pᵀAp)` has derivative
`-(vᵀCv + pᵀHp)`: the reciprocal coupling power cancels. The
stored-energy/dissipation reading additionally requires the
usual positivity of the storage and damping matrices, which
this algebraic identity does not assume. -/
theorem vibroacoustic_port_energy {n m : Type*} [Fintype n]
    [Fintype m] {M K C : Matrix n n ℝ} {A H : Matrix m m ℝ}
    {G : Matrix n m ℝ} (hM : M.IsSymm) (hK : K.IsSymm)
    (hA : A.IsSymm)
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
  have hEv := quad_hasDerivAt (S := M) (u := v) (du := dv) hv t
  have hEx := quad_hasDerivAt (S := K) (u := x) (du := v) hx t
  have hEp := quad_hasDerivAt (S := A) (u := p) (du := dp) hp t
  have hval : (1 / 2 : ℝ) * ((((dv t) ⬝ᵥ (M *ᵥ v t) + (v t) ⬝ᵥ (M *ᵥ dv t))
      + ((v t) ⬝ᵥ (K *ᵥ x t) + (x t) ⬝ᵥ (K *ᵥ v t)))
      + ((dp t) ⬝ᵥ (A *ᵥ p t) + (p t) ⬝ᵥ (A *ᵥ dp t)))
      = -(((v t) ⬝ᵥ (C *ᵥ v t)) + ((p t) ⬝ᵥ (H *ᵥ p t))) := by
    have e1 : ((v t) ⬝ᵥ (M *ᵥ dv t)) + ((v t) ⬝ᵥ (C *ᵥ v t))
        + ((v t) ⬝ᵥ (K *ᵥ x t)) - ((v t) ⬝ᵥ (G *ᵥ p t)) = 0 := by
      have h := congrArg (dotProduct (v t)) (hstruct t)
      rw [dotProduct_sub, dotProduct_add, dotProduct_add, dotProduct_zero] at h
      exact h
    have e2 : ((p t) ⬝ᵥ (A *ᵥ dp t)) + ((p t) ⬝ᵥ (H *ᵥ p t))
        + ((p t) ⬝ᵥ (Gᵀ *ᵥ v t)) = 0 := by
      have h := congrArg (dotProduct (p t)) (hacous t)
      rw [dotProduct_add, dotProduct_add, dotProduct_zero] at h
      exact h
    have s1 : (dv t) ⬝ᵥ (M *ᵥ v t) = (v t) ⬝ᵥ (M *ᵥ dv t) :=
      symm_dot_swap hM _ _
    have s2 : (v t) ⬝ᵥ (K *ᵥ x t) = (x t) ⬝ᵥ (K *ᵥ v t) :=
      symm_dot_swap hK _ _
    have s3 : (dp t) ⬝ᵥ (A *ᵥ p t) = (p t) ⬝ᵥ (A *ᵥ dp t) :=
      symm_dot_swap hA _ _
    have hc : (v t) ⬝ᵥ (G *ᵥ p t) = (p t) ⬝ᵥ (Gᵀ *ᵥ v t) :=
      couple_dot_swap _ _
    linarith
  have hE : HasDerivAt
      (fun τ => (1 / 2)
        * ((v τ) ⬝ᵥ (M *ᵥ v τ) + (x τ) ⬝ᵥ (K *ᵥ x τ)
          + (p τ) ⬝ᵥ (A *ᵥ p τ)))
      ((1 / 2) * ((((dv t) ⬝ᵥ (M *ᵥ v t) + (v t) ⬝ᵥ (M *ᵥ dv t))
        + ((v t) ⬝ᵥ (K *ᵥ x t) + (x t) ⬝ᵥ (K *ᵥ v t)))
        + ((dp t) ⬝ᵥ (A *ᵥ p t) + (p t) ⬝ᵥ (A *ᵥ dp t)))) t :=
    HasDerivAt.const_mul _ ((hEv.add hEx).add hEp)
  rw [hval] at hE
  exact hE

end Mechanics.Vibroacoustic
