/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.SemialgebraicTriviality
import Mathlib.Tactic.Linarith

/-! # General graph/domain and changing-fibre checks

Reciprocal is a continuous semialgebraic map on a genuine nonzero domain,
so the interface reaches beyond polynomial maps. The square map has one
point over zero and two over one, checking that the actual fibres retain
the change which requires a base partition in Hardt's theorem.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.SemialgebraicTriviality

open Set TauCeti MvPolynomial
open MathlibExt.AlgebraicGeometry.SemialgebraicTriviality

def square (x : RealSpace 1) : RealSpace 1 := fun _ ↦ (x 0) ^ 2

example : fiber Set.univ square (0 : RealSpace 1) = {0} := by
  ext x
  simp only [fiber, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    have hsq : (x 0) ^ 2 = 0 := congrFun h 0
    have hzero : x 0 = 0 := by simpa only [pow_two, mul_eq_zero, or_self] using hsq
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hzero
  · rintro rfl
    ext i
    simp [square]

example : fiber Set.univ square (1 : RealSpace 1) = {1, -1} := by
  ext x
  simp only [fiber, Set.mem_inter_iff, Set.mem_univ, true_and,
    Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hsq : (x 0) ^ 2 = 1 := congrFun h 0
    have hmul : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with hp | hn
    · left
      have hzero : x 0 = 1 := sub_eq_zero.mp hp
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hzero
    · right
      have hzero : x 0 = -1 := by linarith
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hzero
  · rintro (rfl | rfl) <;> ext i <;> simp [square]

def nonzeroDomain : Set (RealSpace 1) := {x | x 0 ≠ 0}

def reciprocal (x : RealSpace 1) : RealSpace 1 := fun _ ↦ (x 0)⁻¹

example : IsSemialgebraicOn reciprocal nonzeroDomain := by
  have hs : IsSemialgebraic nonzeroDomain := by
    simpa [nonzeroDomain] using
      isSemialgebraic_eval_ne_zero (X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ)
  refine isSemialgebraicOn_of_forall_eq_iff hs
    (fun _ : Fin 1 ↦ X (Sum.inl (0 : Fin 1)) * X (Sum.inr (0 : Fin 1)) - 1) ?_
  intro x hx y
  have hx0 : x 0 ≠ 0 := hx
  simp only [map_sub, map_mul, eval_X, map_one, Sum.elim_inl, Sum.elim_inr,
    forall_const, sub_eq_zero]
  constructor
  · intro h
    have h0 : (x 0)⁻¹ = y 0 := congrFun h 0
    rw [← h0, mul_inv_cancel₀ hx0]
  · intro h
    have h0 : (x 0)⁻¹ = y 0 := by
      calc
        (x 0)⁻¹ = (x 0)⁻¹ * (x 0 * y 0) := by rw [h, mul_one]
        _ = y 0 := by rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [reciprocal, hi] using h0

example : ContinuousOn reciprocal nonzeroDomain := by
  apply continuousOn_pi.mpr
  intro i x hx
  exact ((continuous_apply (0 : Fin 1)).continuousAt.inv₀ hx).continuousWithinAt

end MathlibExtTest.AlgebraicGeometry.SemialgebraicTriviality
