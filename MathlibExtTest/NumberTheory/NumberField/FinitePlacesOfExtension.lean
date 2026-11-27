/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NumberField.FinitePlacesOfExtension

open IsDedekindDomain NumberField Real

-- The identity at one place, for an arbitrary extension of number fields.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w.asIdeal.LiesOver v.asIdeal),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L * log (max 1 (HeightOneSpectrum.adicAbv K v x)) :=
  sum_log_max_one_adicAbv_liesOver K L v x

-- The identity over all places.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] (x : K) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L *
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), log (max 1 (HeightOneSpectrum.adicAbv K v x)) :=
  finsum_log_max_one_adicAbv K L x

-- The trivial extension `ℚ/ℚ`: degree one.
example (x : ℚ) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 ℚ),
        log (max 1 (HeightOneSpectrum.adicAbv ℚ w (algebraMap ℚ ℚ x))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ℚ), log (max 1 (HeightOneSpectrum.adicAbv ℚ v x)) := by
  rw [finsum_log_max_one_adicAbv ℚ ℚ x, Module.finrank_self, Nat.cast_one, one_mul]

-- `log max(1, a^n) = n log max(1, a)`: `log max(1, 2³) = 3 log 2`, and `max(1, (1/2)³) = 1`.
example : log (max 1 ((2 : ℝ) ^ 3)) = 3 * log 2 := by
  rw [log_max_one_pow (by norm_num) 3, max_eq_right (by norm_num)]
  norm_num

example : log (max 1 ((1 / 2 : ℝ) ^ 3)) = 0 := by
  rw [log_max_one_pow (by norm_num) 3, max_eq_left (by norm_num), log_one, mul_zero]
