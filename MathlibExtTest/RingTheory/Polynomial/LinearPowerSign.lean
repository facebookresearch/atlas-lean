/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.LinearPowerSign

@[expose] public section

open Polynomial

namespace LinearPowerSignTest

/-- Exact-source consumer, with the original binders. -/
theorem exactSource
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (hg : 1 ≤ g) (P : ℚ[X]) (a : ℚ)
    (ha : a = 1 ∨ a = -1)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (r : ℚ_[ℓ])
    (hP : P.map (algebraMap ℚ ℚ_[ℓ]) =
      C (algebraMap ℚ ℚ_[ℓ] a) * (X + C r) ^ g) :
    r = 1 ∨ r = -1 :=
  Polynomial.eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
    ℓ g hg P a ha h0 r hP

/-- Boundary: the hypothesis `1 ≤ g` cannot be dropped. For `g = 0`, the
constant polynomial `1` has the required shape with shift `5`, yet
`5 ≠ ±1` in `ℚ_[2]`. -/
example : ¬ ∀ (r : ℚ_[2]),
    (1 : ℚ[X]).map (algebraMap ℚ ℚ_[2]) =
        C (algebraMap ℚ ℚ_[2] (1 : ℚ)) * (X + C r) ^ 0 →
      r = 1 ∨ r = -1 := by
  intro h
  have h5 := h 5 (by simp)
  rcases h5 with h1 | h1
  · have : (5 : ℚ_[2]) ≠ 1 := by norm_num
    exact this h1
  · have : (5 : ℚ_[2]) ≠ -1 := by norm_num
    exact this h1

end LinearPowerSignTest
