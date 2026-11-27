/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerPolynomialFormulasEulerPolyGenRecurrence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Low-degree consequences of the recurrence for Euler polynomials of order α

The recurrence gives the first and second Euler polynomials of order α.
-/

open Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

namespace MathlibExtTest.NumberTheory.EulerPolynomialFormulasEulerPolyGenRecurrence

example (α : ℂ) : eulerPolyGen α 1 = X - C (α / 2) := by
  rw [eulerPolyGen_recurrence α 1 (by decide)]
  simp [eulerPolyGen, eulerNumGen, eulerNumGenAux]

example (α : ℂ) : eulerPolyGen α 2 = (X - C (α / 2)) ^ 2 - C (α / 4) := by
  have h1 : eulerPolyGen α 1 = X - C (α / 2) := by
    rw [eulerPolyGen_recurrence α 1 (by decide)]
    simp [eulerPolyGen, eulerNumGen, eulerNumGenAux]
  have h0 : eulerPolyGen α 0 = 1 := by
    simp [eulerPolyGen, eulerNumGen, eulerNumGenAux]
  have he : (eulerPoly 1).eval (0 : ℚ) = -1 / 2 := by
    norm_num [eulerPoly, Polynomial.bernoulli, Finset.sum_range_succ, Nat.choose]
  have hc : α / 2 * (1 / 2) = α / 4 := by ring
  rw [eulerPolyGen_recurrence α 2 (by decide)]
  norm_num [h1, h0, he, Finset.sum_range_succ]
  rw [← pow_two, ← C_mul, hc]
  ring

end MathlibExtTest.NumberTheory.EulerPolynomialFormulasEulerPolyGenRecurrence
