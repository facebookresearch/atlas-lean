/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.QuarticNormSquare
import Mathlib.Tactic.IntervalCases

@[expose] public section

set_option autoImplicit false

/-- Exact-source consumer, using the original binders verbatim. -/
example (D c : ℤ) (hD : 0 < D) (hc : 0 < c)
    (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous 4)
    (hF : ∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P)
    (hone : F ![1, 0, 0, 0] = 1)
    (hmul : ∀ v w : Fin 4 → ℤ,
      F ![v 0 * w 0 + D * (v 1 * w 1) + c * (v 2 * w 2) + D * c * (v 3 * w 3),
          v 0 * w 1 + v 1 * w 0 + c * (v 2 * w 3 + v 3 * w 2),
          v 0 * w 2 + v 2 * w 0 + D * (v 1 * w 3 + v 3 * w 1),
          v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1] = F v * F w)
    (hzd : ∀ r : ℤ, r ^ 2 = D * c → F ![r, 0, 0, 1] = 0) :
    IsSquare D ∨ IsSquare c :=
  MvPolynomial.isSquare_or_isSquare_of_isHomogeneous_of_forall_eval_mul_eq
    D c hD hc F P hP hF hone hmul hzd

/-- Boundary example: dropping the normalization allows a non-square
parameter with the zero encoding. -/
example : ¬ (∀ (F : (Fin 4 → ℤ) → ℕ) (P : MvPolynomial (Fin 4) ℚ),
    P.IsHomogeneous 4 →
    (∀ v : Fin 4 → ℤ, (F v : ℚ) = MvPolynomial.eval (fun i => (v i : ℚ)) P) →
    (∀ v w : Fin 4 → ℤ,
      F ![v 0 * w 0 + 2 * (v 1 * w 1) + 3 * (v 2 * w 2) + 2 * 3 * (v 3 * w 3),
          v 0 * w 1 + v 1 * w 0 + 3 * (v 2 * w 3 + v 3 * w 2),
          v 0 * w 2 + v 2 * w 0 + 2 * (v 1 * w 3 + v 3 * w 1),
          v 0 * w 3 + v 3 * w 0 + v 1 * w 2 + v 2 * w 1] = F v * F w) →
    (∀ r : ℤ, r ^ 2 = 2 * 3 → F ![r, 0, 0, 1] = 0) →
    IsSquare (2 : ℤ) ∨ IsSquare (3 : ℤ)) := by
  intro h
  have h2 : ¬ IsSquare (2 : ℤ) := by
    rintro ⟨r, hr⟩
    have hsq : r.natAbs * r.natAbs = 2 := by
      have h := congrArg Int.natAbs hr
      simpa [Int.natAbs_mul] using h.symm
    have hle : r.natAbs ≤ 1 := by
      by_contra hle
      push_neg at hle
      have hge : 2 * 2 ≤ r.natAbs * r.natAbs := Nat.mul_le_mul hle hle
      omega
    interval_cases r.natAbs <;> norm_num at hsq
  have h3 : ¬ IsSquare (3 : ℤ) := by
    rintro ⟨r, hr⟩
    have hsq : r.natAbs * r.natAbs = 3 := by
      have h := congrArg Int.natAbs hr
      simpa [Int.natAbs_mul] using h.symm
    have hle : r.natAbs ≤ 1 := by
      by_contra hle
      push_neg at hle
      have hge : 2 * 2 ≤ r.natAbs * r.natAbs := Nat.mul_le_mul hle hle
      omega
    interval_cases r.natAbs <;> norm_num at hsq
  exact (h (fun _ => 0) 0 (MvPolynomial.isHomogeneous_zero (Fin 4) ℚ 4) (by simp) (by simp)
    (by simp)).elim h2 h3
