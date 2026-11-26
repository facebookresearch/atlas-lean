/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.WaterhouseTracesRamanujanIffNontrivialZerosReEqHalf

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.WaterhouseTracesRamanujanIffNontrivialZerosReEqHalf

private lemma symm_zero : (0 : Matrix (Fin 1) (Fin 1) ℤ).IsSymm := by decide

private lemma charpoly_zero_one :
    (0 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = Polynomial.X := by
  simp [Matrix.charpoly_zero]

private lemma aroots_zero_one :
    (0 : Matrix (Fin 1) (Fin 1) ℤ).charpoly.aroots ℂ = {0} := by
  rw [charpoly_zero_one, Polynomial.aroots_X]

private lemma bound_zero :
    ∀ μ ∈ (0 : Matrix (Fin 1) (Fin 1) ℤ).charpoly.aroots ℂ,
      μ ≠ ((2 : ℕ) : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt 2 := by
  intro μ hμ _
  rw [aroots_zero_one] at hμ
  simp at hμ
  subst hμ
  simp only [norm_zero]
  positivity

/-- The criterion applied to the `1 × 1` zero matrix at `q = 2`: every solution of
`1 + 2 ^ (1 - 2 * s) = 0` has real part `1 / 2`. -/
example (s : ℂ) (hs : 1 + ((2 : ℕ) : ℂ) ^ (1 - 2 * s) = 0) : s.re = 1 / 2 := by
  have hRHS := (MetaMathlibExt.ramanujan_iff_nontrivial_zeros_re_eq_half
    (by norm_num : 2 ≤ 2) (0 : Matrix (Fin 1) (Fin 1) ℤ) symm_zero).mp bound_zero
  have hmem : (0 : ℂ) ∈ (0 : Matrix (Fin 1) (Fin 1) ℤ).charpoly.aroots ℂ := by
    rw [aroots_zero_one]
    simp
  have heq0 : 1 - (0 : ℂ) * ((2 : ℕ) : ℂ) ^ (-s) + ((2 : ℕ) : ℂ) ^ (1 - 2 * s) = 0 := by
    simpa using hs
  exact hRHS 0 hmem (by norm_num) s heq0

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.WaterhouseTracesRamanujanIffNontrivialZerosReEqHalf
