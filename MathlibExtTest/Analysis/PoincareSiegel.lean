/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PoincareSiegel
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MathlibExtTest.Analysis.PoincareSiegel

open MathlibExt.Analysis.PoincareSiegelWanted.ComplexAnalysis Polynomial
open scoped Topology

-- A genuine Diophantine multiplier, including approximations with negative denominator.
private theorem sqrt_two_diophantine : IsDiophantine (Real.sqrt 2) := by
  let P := (X ^ 2 - C 2 : ℤ[X])
  have hP : P ≠ 0 := X_pow_sub_C_ne_zero (by decide) _
  have hroot : eval (Real.sqrt 2) (P.map (algebraMap ℤ ℝ)) = 0 := by
    simp [P, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨A, hA, h⟩ := Liouville.exists_pos_real_of_irrational_root irrational_sqrt_two hP hroot
  have hb (p : ℤ) (b : ℕ) :
      A⁻¹ / (b + 1 : ℝ) ^ P.natDegree ≤ |Real.sqrt 2 - p / (b + 1)| := by
    rw [div_le_iff₀ (by positivity), inv_le_iff_one_le_mul₀ hA]
    simpa only [mul_left_comm, mul_assoc, mul_comm] using h p b
  refine ⟨A⁻¹, P.natDegree, inv_pos.mpr hA, fun p q hq => ?_⟩
  rw [Real.rpow_natCast]
  cases q with
  | ofNat q =>
    cases q with
    | zero => exact (hq rfl).elim
    | succ b =>
      simpa [abs_of_nonneg (by positivity : 0 ≤ (b : ℝ) + 1)] using hb p b
  | negSucc b =>
    simpa only [Int.cast_negSucc, Nat.cast_succ, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (b : ℝ) + 1), div_neg, Int.cast_neg, neg_div]
      using hb (-p) b

-- Apply the theorem to a nonlinear polynomial with the concrete rotation number above.
example :
    let lam := Complex.exp (2 * Real.pi * Complex.I * (Real.sqrt 2 : ℂ))
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), lam * u z + (u z) ^ 2 = u (lam * z) := by
  intro lam
  apply poincare_siegel (Real.sqrt 2) sqrt_two_diophantine lam rfl (fun z => lam * z + z ^ 2)
  · fun_prop
  · simp
  · have h := hasDerivAt_id (0 : ℂ)
    simpa [Pi.add_def, Pi.pow_def, Function.id_def] using ((h.const_mul lam).add (h.pow 2)).deriv

-- A rational rotation cannot satisfy the positive lower bound.
example : ¬ IsDiophantine (3 / 2) := by
  rintro ⟨C, τ, hC, h⟩
  have hbad := h 3 2 (by decide)
  norm_num at hbad
  exact (not_le_of_gt (div_pos hC (Real.rpow_pos_of_pos (by norm_num) τ))) hbad

end MathlibExtTest.Analysis.PoincareSiegel
