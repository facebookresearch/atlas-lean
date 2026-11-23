/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EisensteinQCoeffIntegral

@[expose] public section

-- exactSource consumer: the original binders apply verbatim.
example (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) (m : ℕ) (hm : 0 < m) :
    ∃ (x : ℤ) (s : ℕ), ¬ p ∣ s ∧
      (x : ℂ) = s * (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E hk)) ∧
      (p : ℤ) ∣ x :=
  ModularForm.eisenstein_qCoeff_p_integral_dvd p hk hk2 hpk m hm

-- Boundary: the hypothesis `0 < m` matters. For `m = 0` the coefficient is `1`, and
-- with `p = 5` and `k = 4` the stated conclusion would force `5 ∣ x` and `x = s`
-- with `¬ 5 ∣ s`, which is impossible.
example :
    ¬ ∃ (x : ℤ) (s : ℕ), ¬ (5 : ℕ) ∣ s ∧
      (x : ℂ) = s * (PowerSeries.coeff 0)
        (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E (by norm_num : 3 ≤ 4))) ∧
      (5 : ℤ) ∣ x := by
  rintro ⟨x, s, hs, hx, h5⟩
  have h0 : (PowerSeries.coeff 0)
      (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E (by norm_num : 3 ≤ 4))) = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by norm_num)
  rw [h0, mul_one] at hx
  have hxs : x = (s : ℤ) := by exact_mod_cast hx
  rw [hxs] at h5
  exact hs (by exact_mod_cast h5)
