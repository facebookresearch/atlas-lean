/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.CriticalValuesUnramified
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Tests for a polynomial map being unramified away from its critical values

These examples exercise `Polynomial.formallyUnramified_awayMap_compRingHom` and its
characteristic-zero form over `ℂ`, for `p = X ^ 2`, whose only finite critical value is `0`,
and for `p = X`, which has none.
-/

@[expose] public section

open Polynomial

/-- The only finite critical value of `z ↦ z ^ 2` over `ℂ` is `0`. -/
example : (derivative (X ^ 2 : ℂ[X])).roots.toFinset.image (fun r => (X ^ 2 : ℂ[X]).eval r) =
    {0} := by
  have : derivative (X ^ 2 : ℂ[X]) = C 2 * X := by
    rw [derivative_X_pow]
    simp
  rw [this, roots_C_mul _ (by norm_num), roots_X]
  simp

/-- `z ↦ z ^ 2` on `ℂ`, restricted over the complement of its critical values. -/
example : (Localization.awayMap (compRingHom (X ^ 2 : ℂ[X]))
    (∏ c ∈ (derivative (X ^ 2 : ℂ[X])).roots.toFinset.image (fun r => (X ^ 2 : ℂ[X]).eval r),
      (X - C c))).FormallyUnramified :=
  formallyUnramified_awayMap_compRingHom_of_natDegree_pos _ (by simp)

/-- `z ↦ z ^ 2` on `ℂ`, from the hypothesis `p' ≠ 0`. -/
example : (Localization.awayMap (compRingHom (X ^ 2 : ℂ[X]))
    (∏ c ∈ (derivative (X ^ 2 : ℂ[X])).roots.toFinset.image (fun r => (X ^ 2 : ℂ[X]).eval r),
      (X - C c))).FormallyUnramified :=
  formallyUnramified_awayMap_compRingHom _ (by simp)

/-- The identity `z ↦ z` has no critical values and is unramified everywhere. -/
example : (Localization.awayMap (compRingHom (X : ℂ[X]))
    (∏ c ∈ (derivative (X : ℂ[X])).roots.toFinset.image (fun r => (X : ℂ[X]).eval r),
      (X - C c))).FormallyUnramified :=
  formallyUnramified_awayMap_compRingHom _ (by simp)
