/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Goormaghtigh
import Mathlib.Algebra.Ring.GeomSum

/-! # Tests for the abc bound on Goormaghtigh numbers -/

-- At the length-five boundary, the theorem applies to the quotient form of both repunits.
example (habc : ∀ ε : ℝ, 0 < ε →
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
      (∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ)}.Finite) :
    {N : ℕ | ∃ x y m : ℕ, 2 ≤ x ∧ x < y ∧
      N = (x ^ m - 1) / (x - 1) ∧ N = (y ^ 5 - 1) / (y - 1)}.Finite := by
  apply (MetaMathlibExt.goormaghtigh_numbers_length_ge_five_finite_of_abc (habc := habc)).subset
  rintro N ⟨x, y, m, hx, hxy, hNx, hNy⟩
  exact ⟨x, y, m, 5, hx, hxy, le_rfl, hNx.trans (Nat.geomSum_eq hx m).symm,
    hNy.trans (Nat.geomSum_eq (by omega) 5).symm⟩
