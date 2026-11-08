/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.Deriv.Mul

public import MathlibExt.NumberTheory.PolynomialTL1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MetaMathlibExt

open Polynomial

example (S : ℕ → Polynomial ℝ) (l : ℕ) (x : ℝ) :
    TIntegrand S l x =
      (8 * x ^ l - Polynomial.aeval x (S l)) / (Real.sqrt x * (4 - x)) := rfl

example (S T : ℕ → Polynomial ℝ) (hzero : T 0 = 0)
    (hdegree : ∀ l : ℕ, 1 ≤ l → (T l).natDegree = l - 1 ∧ T l ≠ 0)
    (hderiv : ∀ l : ℕ, 1 ≤ l → ∀ x : ℝ, 0 < x → x < 4 →
      HasDerivAt (fun y : ℝ => 2 * Real.sqrt y * Polynomial.aeval y (T l))
        (TIntegrand S l x) x) : IsPolyTFamily S T :=
  ⟨hzero, hdegree, hderiv⟩

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T) : T 0 = 0 := h.1

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T)
    (l : ℕ) (hl : 1 ≤ l) : (T l).natDegree = l - 1 :=
  (h.2.1 l hl).1

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T)
    (l : ℕ) (hl : 1 ≤ l) : T l ≠ 0 :=
  (h.2.1 l hl).2


/-- A concrete family exercising the `l = 0` convention and the `l - 1`
degree shift without assuming the fields of `IsPolyTFamily`. -/
private noncomputable def concreteT (l : ℕ) : Polynomial ℝ :=
  if l = 0 then 0 else X ^ (l - 1)

private noncomputable def concreteS (l : ℕ) : Polynomial ℝ :=
  C 8 * X ^ l - (C 4 - X) * concreteT l -
    C 2 * X * (C 4 - X) * (concreteT l).derivative

example : IsPolyTFamily concreteS concreteT := by
  constructor
  · simp [concreteT]
  constructor
  · intro l hl
    have hl0 : l ≠ 0 := by omega
    simp [concreteT, hl0]
  · intro l hl x hx hx4
    have hl0 : l ≠ 0 := by omega
    have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have h4x : 4 - x ≠ 0 := by linarith
    rw [show concreteT l = X ^ (l - 1) by simp [concreteT, hl0]]
    apply HasDerivAt.congr_deriv
      (((Real.hasDerivAt_sqrt hx.ne').const_mul 2).mul
        ((X ^ (l - 1)).hasDerivAt_aeval x))
    simp only [TIntegrand, concreteS, map_sub, map_mul, map_pow,
      aeval_C, aeval_X]
    simp only [concreteT, hl0, if_false]
    field_simp
    rw [Real.sq_sqrt hx.le]
    simp
    ring

end MetaMathlibExt
