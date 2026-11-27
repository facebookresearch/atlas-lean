/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.NormNum

/-!
For the critical presentation of x cubed, I=(x squared), the d-critical
function class is nonzero modulo I squared, although every field point
annihilates it. Replacing the defining quotient by O/I or O/Irad loses
this class. The derivative check uses the actual universal derivation.
-/

open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions
open MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels
open Polynomial

noncomputable section

private def criticalIdeal : Ideal ℚ[X] := Ideal.span {(X : ℚ[X]) ^ 2}

private theorem square_mem : (X : ℚ[X]) ^ 2 ∈ criticalIdeal :=
  Ideal.subset_span (by simp)

private theorem derivative_mem :
    KaehlerDifferential.D ℚ ℚ[X] ((X : ℚ[X]) ^ 3) ∈
      idealDifferentials ℚ ℚ[X] criticalIdeal := by
  rw [Derivation.leibniz_pow]
  have h : (X : ℚ[X]) ^ 2 • KaehlerDifferential.D ℚ ℚ[X] X ∈
      idealDifferentials ℚ ℚ[X] criticalIdeal :=
    Submodule.smul_mem_smul square_mem (Submodule.mem_top)
  norm_num only [Nat.reduceSub]
  rw [← Nat.cast_smul_eq_nsmul ℚ[X] 3]
  exact Submodule.smul_mem (idealDifferentials ℚ ℚ[X] criticalIdeal) (3 : ℚ[X]) h

private theorem reduction_mem : (X : ℚ[X]) ^ 3 ∈ criticalIdeal.radical :=
  Ideal.le_radical (by
    simpa only [pow_succ'] using criticalIdeal.mul_mem_left X square_mem)

private theorem cube_not_square : (X : ℚ[X]) ^ 3 ∉ criticalIdeal ^ 2 := by
  intro h
  change (X : ℚ[X]) ^ 3 ∈ (Ideal.span {(X : ℚ[X]) ^ 2}) ^ 2 at h
  rw [Ideal.span_singleton_pow, ← pow_mul] at h
  have hd : (X : ℚ[X]) ^ 4 ∣ X ^ 3 := Ideal.mem_span_singleton.mp h
  have hc := Polynomial.X_pow_dvd_iff.mp hd 3 (by decide)
  norm_num at hc

example : criticalClass criticalIdeal ((X : ℚ[X]) ^ 3) derivative_mem reduction_mem ≠ 0 := by
  rw [ne_eq, criticalClass_eq_zero_iff]
  exact cube_not_square

example (K : Type) [Field K] (f : ℚ[X] →+* K)
    (vanishes : ∀ a ∈ criticalIdeal, f a = 0) : f (X ^ 3) = 0 := by
  have h : f X * f X = 0 := by
    simpa only [map_pow, pow_two, map_mul] using vanishes _ square_mem
  have hx := mul_self_eq_zero.mp h
  simp [map_pow, hx]
