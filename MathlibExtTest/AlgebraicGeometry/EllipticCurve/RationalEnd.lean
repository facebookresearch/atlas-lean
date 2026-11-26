/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.RationalEnd
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt

open WeierstrassCurve

section EvalEvalBC

open Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] (x y : k)

/-- `evalEvalBC` evaluates the inner variable at `x`, the outer one at `y`, and maps constants
along `algebraMap F k`. -/
example : evalEvalBC k (C X : F[X][Y]) x y = x := by
  simp [evalEvalBC, evalEval_C]

example : evalEvalBC k (X : F[X][Y]) x y = y := by
  simp [evalEvalBC, evalEval_X]

example (a : F) : evalEvalBC k (C (C a) : F[X][Y]) x y = algebraMap F k a := by
  simp [evalEvalBC, evalEval_C]

end EvalEvalBC

example {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    [IsAlgClosed k] (W : WeierstrassCurve F) :
    (1 : AddMonoid.End (W.baseChange k).toAffine.Point) ∈ rationalEndSubring k W :=
  one_mem_rationalEndSubring k W

/-! A non-geometric additive map is not rational. -/

namespace RationalEndTest

open Complex

/-- The curve `y² = x³ - x` over `ℝ`. -/
private def W : WeierstrassCurve ℝ := ⟨0, 0, 0, -1, 0⟩

private theorem nonsingular_iff (x y : ℂ) :
    (W.baseChange ℂ).toAffine.Nonsingular x y ↔
      y ^ 2 = x ^ 3 - x ∧ (1 - 3 * x ^ 2 ≠ 0 ∨ y ≠ 0) := by
  rw [Affine.nonsingular_iff', Affine.equation_iff]
  simp [W, WeierstrassCurve.baseChange, sub_eq_add_neg]

/-- `P ↦ P - conj P`, an additive endomorphism of the complex points that is not induced by a
morphism: it is nonzero but kills the infinitely many real points. -/
private noncomputable def α :
    (W.baseChange ℂ).toAffine.Point →+ (W.baseChange ℂ).toAffine.Point :=
  AddMonoidHom.id _ - Affine.Point.map (W' := W) Complex.conjAe.toAlgHom

private theorem α_some (x y : ℂ) (h : (W.baseChange ℂ).toAffine.Nonsingular x y) :
    α (.some x y h) = .some x y h - Affine.Point.map (W' := W) Complex.conjAe.toAlgHom
      (.some x y h) := rfl

example : α ∉ rationalHomSet ℂ W W := by
  rintro (h0 | ⟨nX, dX, nY, dY, B, hB, hα⟩)
  · have hP : (W.baseChange ℂ).toAffine.Nonsingular I (1 - I) := by
      rw [nonsingular_iff]
      refine ⟨by ring_nf; simp [I_sq, I_pow_three]; ring, Or.inr ?_⟩
      intro h
      have := congrArg Complex.im h
      simp at this
    have h1 := DFunLike.congr_fun h0 (.some I (1 - I) hP)
    rw [α_some, Affine.Point.map_some, AddMonoidHom.zero_apply, sub_eq_zero] at h1
    have h2 := congrArg Complex.im (Affine.Point.some.inj h1).1
    norm_num at h2
  · obtain ⟨r, hr, hrB⟩ := (Set.Ici_infinite (2 : ℝ)).exists_notMem_finite
      (hB.preimage Complex.ofReal_injective.injOn)
    have hr2 : (2 : ℝ) ≤ r := hr
    have hr0 : 0 ≤ r ^ 3 - r := by
      rw [show r ^ 3 - r = r * (r ^ 2 - 1) by ring]
      exact mul_nonneg (by linarith) (by nlinarith)
    have hP : (W.baseChange ℂ).toAffine.Nonsingular (r : ℂ) (√(r ^ 3 - r) : ℂ) := by
      rw [nonsingular_iff]
      refine ⟨by exact_mod_cast Real.sq_sqrt hr0, Or.inl ?_⟩
      exact_mod_cast (by nlinarith : (1 - 3 * r ^ 2 : ℝ) < 0).ne
    obtain ⟨-, -, h', hαP⟩ := hα _ _ hP hrB
    have hzero : α (.some _ _ hP) = 0 := by
      rw [α_some, Affine.Point.map_some, sub_eq_zero]
      simp
    exact Affine.Point.some_ne_zero h' (hαP ▸ hzero)

end RationalEndTest
