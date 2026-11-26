/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRoots

/-! # Tests for the root formula for the `k`-Padovan–Perrin numbers -/

namespace MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRoots

open Polynomial MetaMathlibExt

-- With `k = 2` and initial values `(v 0, v 1, v 2) = (0, 0, 1)`, the coefficients in
-- `kPadovanPerrin_eq_sum_roots` at `n = 4` evaluate to `A₀ = 0`, `A₁ = 1`, `A₂ = 2`.
example (v : ℕ → ℂ) (hv : (padovanPerrinRecurrence 1 (2 : ℂ) 1 2).IsSolution v)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 1) :
    v 4 = (((X ^ 3 - X - C (2 : ℂ)).roots.map fun x =>
      (x ^ 2 + 2 * x) / (derivative (X ^ 3 - X - C (2 : ℂ))).eval x).sum) := by
  have h := kPadovanPerrin_eq_sum_roots 2 le_rfl v (by simpa using hv) 4 (by omega)
  rw [h0, h1, h2] at h
  simpa using h

-- For the same parameters, `v 4 = v 2 + 2 * v 1 = 1`, so the root sum equals `1`.
example (v : ℕ → ℂ) (hv : (padovanPerrinRecurrence 1 (2 : ℂ) 1 2).IsSolution v)
    (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 1) :
    (((X ^ 3 - X - C (2 : ℂ)).roots.map fun x =>
      (x ^ 2 + 2 * x) / (derivative (X ^ 3 - X - C (2 : ℂ))).eval x).sum) = 1 := by
  have r := ((padovanPerrinRecurrence_isSolution_iff 1 (2 : ℂ) 1 2 (by omega) v).mp hv) 1
  have h4 : v 4 = 1 := by simpa [h0, h1, h2] using r
  have h := kPadovanPerrin_eq_sum_roots 2 le_rfl v (by simpa using hv) 4 (by omega)
  rw [h0, h1, h2, h4] at h
  simpa using h.symm

end MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRoots
