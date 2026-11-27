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
pressure trajectories, in possibly different finite dimensions,
satisfying `K*u - Q*p = f` and
`C*p' + Q^T*u' + H*p = s` for constant symmetric storage
matrices `K` and `C`, the stored quadratic energy
`(1/2) * (u^T K u + p^T C p)` has derivative equal to the input
power `u'^T f + p^T s` minus the dissipation `p^T H p`. The two
coupling powers cancel because the ports carry opposite signs.
This is the algebraic quadratic balance: reading the quadratic
forms as stored energy and dissipation additionally requires
the usual positivity (positive semidefinite storage and
dissipation matrices), which the identity itself does not
assume.

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

private lemma hasDerivAt_dot_mulVec_self {m : Type*} [Fintype m] {A : Matrix m m ℝ}
    (hA : A.IsSymm) {x dx : ℝ → m → ℝ}
    (hx : ∀ i t, HasDerivAt (fun τ => x τ i) (dx t i) t) (t : ℝ) :
    HasDerivAt (fun τ => (x τ) ⬝ᵥ (A *ᵥ x τ)) (2 * ((dx t) ⬝ᵥ (A *ᵥ x t))) t := by
  have hrow : ∀ i, HasDerivAt (fun τ => (A *ᵥ x τ) i) ((A *ᵥ dx t) i) t := by
    intro i
    have hterm : ∀ j ∈ (Finset.univ : Finset m),
        HasDerivAt (fun τ => A i j * x τ j) (A i j * dx t j) t :=
      fun j _ => (hx j t).const_mul (A i j)
    have hsum := HasDerivAt.sum hterm
    have hfun : (∑ j ∈ (Finset.univ : Finset m), fun τ => A i j * x τ j)
        = (fun τ => (A *ᵥ x τ) i) := by
      funext τ
      simp [Matrix.mulVec_apply, dotProduct, Finset.sum_apply]
    have hval : (∑ j ∈ (Finset.univ : Finset m), A i j * dx t j)
        = (A *ᵥ dx t) i := by
      simp [Matrix.mulVec_apply, dotProduct]
    rw [hfun, hval] at hsum
    exact hsum
  have hprod : ∀ i ∈ (Finset.univ : Finset m),
      HasDerivAt (fun τ => x τ i * (A *ᵥ x τ) i)
        (dx t i * (A *ᵥ x t) i + x t i * (A *ᵥ dx t) i) t := by
    intro i _
    exact (hx i t).mul (hrow i)
  have hsum2 := HasDerivAt.sum hprod
  have hfun2 : (∑ i ∈ (Finset.univ : Finset m), fun τ => x τ i * (A *ᵥ x τ) i)
      = (fun τ => (x τ) ⬝ᵥ (A *ᵥ x τ)) := by
    funext τ
    simp [dotProduct, Finset.sum_apply]
  have hsymm : (x t) ⬝ᵥ (A *ᵥ dx t) = (dx t) ⬝ᵥ (A *ᵥ x t) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.IsSymm.eq hA,
      dotProduct_comm]
  have hval2 : (∑ i ∈ (Finset.univ : Finset m),
        (dx t i * (A *ᵥ x t) i + x t i * (A *ᵥ dx t) i))
      = 2 * ((dx t) ⬝ᵥ (A *ᵥ x t)) := by
    rw [Finset.sum_add_distrib]
    have e1 : (∑ i ∈ (Finset.univ : Finset m), dx t i * (A *ᵥ x t) i)
        = (dx t) ⬝ᵥ (A *ᵥ x t) := by simp [dotProduct]
    have e2 : (∑ i ∈ (Finset.univ : Finset m), x t i * (A *ᵥ dx t) i)
        = (x t) ⬝ᵥ (A *ᵥ dx t) := by simp [dotProduct]
    rw [e1, e2, hsymm]
    ring
  rw [hfun2, hval2] at hsum2
  exact hsum2

/-- Finite poroelastic port-energy identity, with distinct
displacement and pressure index types. Along differentiable
trajectories `u` (displacement, `m` coordinates) and `p`
(pressure, `n` coordinates) with supplied derivative functions
satisfying, at every time, `K*u - Q*p = f` and
`C*p' + Qᵀ*u' + H*p = s`, for constant symmetric storage
matrices `K` (`m × m`) and `C` (`n × n`) and rectangular
coupling `Q` (`m × n`), the stored quadratic energy
`1/2 * (uᵀKu + pᵀCp)` has derivative equal to input power
`u'ᵀf + pᵀs` minus dissipation `pᵀHp`. The opposite signs of
the two coupling terms are essential. Reading the quadratic
forms as energy and dissipation uses the usual positivity of
the physical model; the identity itself needs only symmetry. -/
theorem poroelastic_port_energy {m n : Type*} [Fintype m]
    [Fintype n] {K : Matrix m m ℝ} {Q : Matrix m n ℝ}
    {C H : Matrix n n ℝ} (hK : K.IsSymm) (hC : C.IsSymm)
    {u du f : ℝ → m → ℝ} {p dp s : ℝ → n → ℝ}
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
  have hKu := hasDerivAt_dot_mulVec_self hK hu t
  have hCp := hasDerivAt_dot_mulVec_self hC hp t
  have hE := (hKu.add hCp).const_mul (1 / 2 : ℝ)
  have hcoup : (p t) ⬝ᵥ (Qᵀ *ᵥ du t) = (du t) ⬝ᵥ (Q *ᵥ p t) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hCsym : (p t) ⬝ᵥ (C *ᵥ dp t) = (dp t) ⬝ᵥ (C *ᵥ p t) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.IsSymm.eq hC,
      dotProduct_comm]
  have hval : (1 / 2 : ℝ) * (2 * ((du t) ⬝ᵥ (K *ᵥ u t)) + 2 * ((dp t) ⬝ᵥ (C *ᵥ p t)))
      = (du t) ⬝ᵥ (f t) + (p t) ⬝ᵥ (s t) - (p t) ⬝ᵥ (H *ᵥ p t) := by
    have hf : (du t) ⬝ᵥ f t
        = (du t) ⬝ᵥ (K *ᵥ u t) - (du t) ⬝ᵥ (Q *ᵥ p t) := by
      rw [← hmech t, dotProduct_sub]
    have hs : (p t) ⬝ᵥ s t
        = (p t) ⬝ᵥ (C *ᵥ dp t) + (p t) ⬝ᵥ (Qᵀ *ᵥ du t) + (p t) ⬝ᵥ (H *ᵥ p t) := by
      rw [← hfluid t, dotProduct_add, dotProduct_add]
    rw [hf, hs, hCsym, hcoup]
    ring
  rw [hval] at hE
  exact hE

end Mechanics.Poroelastic
