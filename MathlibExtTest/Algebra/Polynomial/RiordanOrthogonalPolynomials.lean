/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.RiordanOrthogonalPolynomials

namespace MetaMathlibExt

-- The third projection exposes the coefficient recurrence characterization.
example (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hRiordan : PowerSeries.coeff 0 h = 0 ∧ PowerSeries.coeff 1 h ≠ 0 ∧
      PowerSeries.coeff 0 d ≠ 0 ∧
      ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) :
    let IsMonicOrthogonalCoeffArray :=
      ∃ P : ℕ → Polynomial ℝ,
        (∀ n k : ℕ, (P n).coeff k = L n k) ∧
        (∀ n : ℕ, (P n).Monic) ∧ Polynomial.IsFormallyOrthogonal P
    IsMonicOrthogonalCoeffArray ↔
      ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
        ∀ N K : ℕ,
          L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
              (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
              s * (if 2 ≤ N then L (N - 2) K else 0) =
            (if K = 0 then
              if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
            else 0) := by
  exact (riordan_coeff_orth_equiv d h L hRiordan).2.2

end MetaMathlibExt
